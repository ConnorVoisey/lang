//! RVSDG (Regionalized Value State Dependence Graph) IR
//!
//! This is an intermediate representation between AST and Cranelift that enables
//! powerful optimizations while maintaining fast compile times.
//!
//! Key design principles:
//! - Structured control flow (no CFG) using regions
//! - SSA values with explicit data dependencies
//! - State dependencies for memory operations
//! - Flat arena storage for cache locality
//! - Zero-cost node iteration

use crate::{
    interner::SharedInterner,
    lexer::Span,
    struct_layout::StructLayoutInfo,
    symbols::SymbolId,
    types::{TypeArena, TypeId},
};
use rustc_hash::FxHashMap;

pub mod builder;
pub mod display;
pub mod graphviz;
pub mod lower;
pub mod node;
pub mod optimize;
pub mod to_cranelift;

// ===== Core ID Types =====

/// Index into Module.functions
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FunctionId(pub usize);

/// Index into Module.globals
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct GlobalId(pub usize);

/// Index into Function.nodes
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub usize);

/// Index into Function.nodes, specifically for region nodes
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct RegionId(pub usize);

/// Represents an SSA value (output of a node)
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct ValueId {
    pub node: NodeId,
    pub output_index: u32,
}

/// Index for struct fields
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FieldId(pub usize);

// ===== Module =====

pub struct Module<'a> {
    pub functions: Vec<Function>,
    pub extern_functions: Vec<ExternFunction>,
    pub types: &'a TypeArena,
    pub interner: SharedInterner,
    pub struct_layout_info: &'a StructLayoutInfo<'a>,
}

pub struct ExternFunction {
    pub id: FunctionId,
    pub name: SymbolId,
    pub param_types: Vec<TypeId>,
    pub return_type: TypeId,
    pub span: Span,
}

// ===== Function =====

pub struct Function {
    pub id: FunctionId,
    pub name: SymbolId,
    pub params: Vec<Parameter>,
    pub return_type: TypeId,
    pub root: NodeId, // Lambda node
    pub span: Span,

    // Flat storage for cache-friendly iteration
    pub nodes: Vec<Node>,
    pub regions: Vec<Region>, // Regions indexed by RegionId

    // Metadata
    pub is_exported: bool,
    pub inline_hint: InlineHint,
}

#[derive(Clone)]
pub struct Parameter {
    pub name: SymbolId,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineHint {
    Never,
    Auto,
    Always,
}

// ===== Node =====

#[derive(Debug)]
pub struct Node {
    pub id: NodeId,
    pub kind: NodeKind,
    pub span: Span,

    pub output_types: Vec<TypeId>,
}

impl Node {
    pub fn inputs(&self) -> smallvec::SmallVec<[ValueId; 4]> {
        use smallvec::smallvec;
        match &self.kind {
            NodeKind::Lambda { .. } => smallvec![],
            NodeKind::Gamma { inputs, .. } => {
                let mut result = smallvec![inputs.condition];
                result.extend_from_slice(&inputs.captured);
                result
            }
            NodeKind::Theta { inputs, .. } => inputs.all_values().collect(),
            NodeKind::Parameter { .. } => smallvec![],
            NodeKind::StateToken => smallvec![],
            NodeKind::Const { .. } => smallvec![],
            NodeKind::Binary { inputs, .. } => smallvec![inputs.left, inputs.right],
            NodeKind::Unary { inputs, .. } => smallvec![inputs.operand],
            NodeKind::Call { inputs, .. } => {
                let mut result = smallvec![inputs.state];
                result.extend_from_slice(&inputs.args);
                result
            }
            NodeKind::Alloc { inputs, .. } => smallvec![inputs.state],
            NodeKind::Load { inputs, .. } => smallvec![inputs.state, inputs.address],
            NodeKind::Store { inputs, .. } => {
                smallvec![inputs.state, inputs.address, inputs.value]
            }
            NodeKind::RegionParam { .. } => smallvec![],
            NodeKind::RegionResult { inputs } => smallvec![inputs.value],
        }
    }

    pub fn has_inputs(&self) -> bool {
        match &self.kind {
            NodeKind::Lambda { .. }
            | NodeKind::Parameter { .. }
            | NodeKind::StateToken
            | NodeKind::Const { .. }
            | NodeKind::RegionParam { .. } => false,
            _ => true,
        }
    }
}

// ===== Input Structs for Type Safety =====

/// Inputs for a Theta (loop) node
///
/// # Semantics
/// - `state`: State token for effect ordering (always present)
/// - `loop_vars`: Additional loop-carried variables (counters, accumulators, etc.)
///   - Each value becomes a region parameter
///   - Region must produce updated values in the same order
///
/// # Region Structure
/// - Parameters: [state_param, ...loop_var_params]
/// - Results: `[condition, state_updated, ...loop_vars_updated]`
///   - First result: Boolean condition (continue if true)
///   - Second result: Updated state token
///   - Remaining results: Updated loop variables (same count and order as loop_vars)
///
/// # Example
/// ```text
/// while (i < 10) { i = i + 1; }
///
/// ThetaInputs {
///     state: initial_state,
///     loop_vars: [i_initial]
/// }
/// Region results: [i_param < 10, state_param, i_param + 1]
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ThetaInputs {
    pub state: ValueId,
    pub loop_vars: Vec<ValueId>,
}

impl ThetaInputs {
    #[inline]
    pub fn new(state: ValueId, loop_vars: Vec<ValueId>) -> Self {
        Self { state, loop_vars }
    }

    /// Get all loop-carried values (state + loop vars) in order
    #[inline]
    pub fn all_values(&self) -> impl Iterator<Item = ValueId> + '_ {
        std::iter::once(self.state).chain(self.loop_vars.iter().copied())
    }

    /// Total count of loop-carried values (state + loop vars)
    #[inline]
    pub fn len(&self) -> usize {
        1 + self.loop_vars.len()
    }

    /// Validate this theta's inputs against its region
    #[cfg(debug_assertions)]
    pub fn validate(&self, region: &Region, _func: &Function) -> Result<(), String> {
        // Check parameter count (state + loop vars)
        let expected_params = 1 + self.loop_vars.len();
        if region.params.len() != expected_params {
            return Err(format!(
                "Theta has {} loop-carried values (state + {} vars) but region has {} parameters",
                expected_params,
                self.loop_vars.len(),
                region.params.len()
            ));
        }

        // Check result count (1 condition + 1 state + N loop vars)
        let expected_results = 1 + 1 + self.loop_vars.len();
        if region.results.len() != expected_results {
            return Err(format!(
                "Theta region has {} results, expected {} (1 condition + 1 state + {} vars)",
                region.results.len(),
                expected_results,
                self.loop_vars.len()
            ));
        }

        // TODO: Check that first result is boolean type

        Ok(())
    }
}

/// Inputs for a Gamma (conditional/if-else) node
///
/// # Semantics
/// - `condition`: Boolean value determining which region executes
/// - `captured`: Values captured from outer scope and passed to all regions
///
/// # Region Structure
/// - Each region receives the captured values as parameters
/// - All regions must produce the same number and types of results
///
/// # Example
/// ```text
/// if (x < 5) { y } else { z }
///
/// GammaInputs {
///     condition: x < 5,
///     captured: [y, z]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GammaInputs {
    pub condition: ValueId,
    pub captured: Vec<ValueId>,
}

impl GammaInputs {
    #[inline]
    pub fn new(condition: ValueId, captured: Vec<ValueId>) -> Self {
        Self {
            condition,
            captured,
        }
    }

    /// All inputs in the order expected by the region
    #[inline]
    pub fn all_inputs(&self) -> impl Iterator<Item = ValueId> + '_ {
        std::iter::once(self.condition).chain(self.captured.iter().copied())
    }
}

/// Inputs for a Binary operation node
///
/// # Semantics
/// - `left`: Left operand
/// - `right`: Right operand
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinaryInputs {
    pub left: ValueId,
    pub right: ValueId,
}

impl BinaryInputs {
    #[inline(always)]
    pub const fn new(left: ValueId, right: ValueId) -> Self {
        Self { left, right }
    }
}

/// Inputs for a Unary operation node
///
/// # Semantics
/// - `operand`: The value to operate on
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct UnaryInputs {
    pub operand: ValueId,
}

impl UnaryInputs {
    #[inline(always)]
    pub const fn new(operand: ValueId) -> Self {
        Self { operand }
    }
}

/// Inputs for a Call node
///
/// # Semantics
/// - `state`: State token for effect ordering
/// - `args`: Function arguments
///
/// # Outputs
/// - [new_state, result]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallInputs {
    pub state: ValueId,
    pub args: Vec<ValueId>,
}

impl CallInputs {
    #[inline]
    pub fn new(state: ValueId, args: Vec<ValueId>) -> Self {
        Self { state, args }
    }

    /// All inputs in order: state first, then args
    #[inline]
    pub fn all_inputs(&self) -> impl Iterator<Item = ValueId> + '_ {
        std::iter::once(self.state).chain(self.args.iter().copied())
    }
}

/// Inputs for an Alloc (memory allocation) node
///
/// # Semantics
/// - `state`: State token for effect ordering
///
/// # Outputs
/// - [new_state, pointer]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct AllocInputs {
    pub state: ValueId,
}

impl AllocInputs {
    #[inline(always)]
    pub const fn new(state: ValueId) -> Self {
        Self { state }
    }
}

/// Inputs for a Load (memory read) node
///
/// # Semantics
/// - `state`: State token for effect ordering
/// - `address`: Pointer to load from
///
/// # Outputs
/// - [new_state, value]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoadInputs {
    pub state: ValueId,
    pub address: ValueId,
}

impl LoadInputs {
    #[inline(always)]
    pub const fn new(state: ValueId, address: ValueId) -> Self {
        Self { state, address }
    }
}

/// Inputs for a Store (memory write) node
///
/// # Semantics
/// - `state`: State token for effect ordering
/// - `address`: Pointer to store to
/// - `value`: Value to store
///
/// # Outputs
/// - [new_state]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StoreInputs {
    pub state: ValueId,
    pub address: ValueId,
    pub value: ValueId,
}

impl StoreInputs {
    #[inline(always)]
    pub const fn new(state: ValueId, address: ValueId, value: ValueId) -> Self {
        Self {
            state,
            address,
            value,
        }
    }
}

/// Inputs for a RegionResult node
///
/// # Semantics
/// - `value`: The value to return from the region
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RegionResultInputs {
    pub value: ValueId,
}

impl RegionResultInputs {
    #[inline(always)]
    pub const fn new(value: ValueId) -> Self {
        Self { value }
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    // ===== Structural Nodes =====
    /// Lambda: Function body
    /// Outputs: [result values...]
    /// Contains: Single region with function body
    Lambda {
        region: RegionId,
        // No inputs
    },

    /// Gamma: Conditional (if/else)
    /// Outputs: [merged_results...]
    /// Contains: N regions (one per branch)
    Gamma {
        regions: Vec<RegionId>, // regions[0] = true branch, regions[1] = false branch
        inputs: GammaInputs,
    },

    /// Theta: Loop
    /// Outputs: [...final_values]
    /// Contains: Single region that's the loop body
    Theta {
        region: RegionId,
        inputs: ThetaInputs,
    },

    // ===== Simple Nodes =====
    /// Simple value node that just passes through a parameter
    Parameter {
        index: usize,
        // No inputs
    },

    /// State token for effect threading
    /// This represents the "world state" that threads through all effectful operations
    /// Outputs: [state]
    StateToken,
    // No inputs
    /// Constant value
    Const {
        value: ConstValue,
        // No inputs
    },

    /// Binary operation
    Binary { op: BinaryOp, inputs: BinaryInputs },

    /// Unary operation
    Unary { op: UnaryOp, inputs: UnaryInputs },

    /// Function call
    /// Outputs: [new_state, result]
    Call {
        function: FunctionId,
        inputs: CallInputs,
    },

    // ===== Memory Operations =====
    /// Allocate memory (heap or stack determined later)
    /// Outputs: [new_state, pointer]
    Alloc { ty: TypeId, inputs: AllocInputs },

    /// Load from memory
    /// Outputs: [new_state, value]
    Load { ty: TypeId, inputs: LoadInputs },

    /// Store to memory
    /// Outputs: [new_state]
    Store { ty: TypeId, inputs: StoreInputs },

    // ===== Region-specific Nodes =====
    /// Region parameter (input to a region)
    RegionParam {
        index: usize,
        // No inputs
    },

    /// Region result (output from a region)
    RegionResult { inputs: RegionResultInputs },
}

// ===== Constants =====

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstValue {
    I32(i64),
    U32(u64),
    Bool(bool),
    String(Vec<u8>), // Null-terminated string data (for both CStr and Str)
}

// ===== Operations =====

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Logical
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Neg,
    Not,
}

// ===== Region =====

/// A region contains a subgraph
pub struct Region {
    pub id: RegionId,
    pub params: Vec<NodeId>, // RegionParam nodes that are inputs to this region
    pub results: Vec<NodeId>, // Result nodes that produce outputs
    pub nodes: Vec<NodeId>,  // All nodes in this region (in topo order)
}

impl<'a> Module<'a> {
    pub fn new(
        types: &'a TypeArena,
        struct_layout_info: &'a StructLayoutInfo,
        interner: SharedInterner,
    ) -> Self {
        Self {
            functions: Vec::new(),
            extern_functions: Vec::new(),
            types,
            interner,
            struct_layout_info,
        }
    }
}

impl Function {
    /// Get a node by ID
    #[inline]
    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.0]
    }

    /// Get a mutable node by ID
    #[inline]
    pub fn node_mut(&mut self, id: NodeId) -> &mut Node {
        &mut self.nodes[id.0]
    }

    /// Iterate over all nodes
    #[inline]
    pub fn iter_nodes(&self) -> impl Iterator<Item = &Node> {
        self.nodes.iter()
    }

    /// Get a region by ID
    #[inline]
    pub fn region(&self, id: RegionId) -> &Region {
        &self.regions[id.0]
    }

    /// Get a mutable region by ID
    #[inline]
    pub fn region_mut(&mut self, id: RegionId) -> &mut Region {
        &mut self.regions[id.0]
    }
}

// ===== Hash-Consing Support =====

/// Key for hash-consing pure operations
/// Two nodes are equivalent if they have the same kind, inputs, and output types
#[derive(Hash, Eq, PartialEq, Clone)]
pub(crate) struct NodeKey {
    pub kind: NodeKeyKind,
    pub output_types: Vec<TypeId>,
}

#[derive(Hash, Eq, PartialEq, Clone)]
pub(crate) enum NodeKeyKind {
    Const(ConstValue),
    Binary { op: BinaryOp, inputs: BinaryInputs },
    Unary { op: UnaryOp, inputs: UnaryInputs },
    StructFieldAddr { field: FieldId },
}
