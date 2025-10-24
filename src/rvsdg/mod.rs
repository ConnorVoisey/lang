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

    // Type information for each output
    pub output_types: Vec<TypeId>,

    // Inputs as edges
    pub inputs: Vec<ValueId>,
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    // ===== Structural Nodes =====
    /// Lambda: Function body
    /// Inputs: []
    /// Outputs: [result values...]
    /// Contains: Single region with function body
    Lambda { region: RegionId },

    /// Gamma: Conditional (if/else)
    /// Inputs: [condition, ...captured_values]
    /// Outputs: [merged_results...]
    /// Contains: N regions (one per branch)
    Gamma {
        regions: Vec<RegionId>, // regions[0] = true branch, regions[1] = false branch
    },

    /// Theta: Loop
    /// Inputs: [...initial_values]
    /// Outputs: [...final_values]
    /// Contains: Single region that's the loop body
    Theta { region: RegionId },

    // ===== Simple Nodes =====
    /// Simple value node that just passes through a parameter
    Parameter { index: usize },

    /// State token for effect threading
    /// This represents the "world state" that threads through all effectful operations
    /// Inputs: []
    /// Outputs: [state]
    StateToken,

    /// Constant value
    Const { value: ConstValue },

    /// Binary operation
    Binary {
        op: BinaryOp,
        // Inputs: [lhs, rhs]
    },

    /// Unary operation
    Unary {
        op: UnaryOp,
        // Inputs: [operand]
    },

    /// Function call
    Call {
        function: FunctionId,
        // Inputs: [state, ...args]
        // Outputs: [new_state, result]
    },

    // ===== Memory Operations =====
    /// Allocate memory (heap or stack determined later)
    /// Inputs: [state]
    /// Outputs: [new_state, pointer]
    Alloc { ty: TypeId },

    /// Load from memory
    /// Inputs: [state, address]
    /// Outputs: [new_state, value]
    Load { ty: TypeId },

    /// Store to memory
    /// Inputs: [state, address, value]
    /// Outputs: [new_state]
    Store { ty: TypeId },

    // ===== Struct Operations =====
    /// Get struct field address
    /// Inputs: [struct_ptr]
    /// Outputs: [field_ptr]
    StructFieldAddr { field: FieldId },

    /// Load struct field
    /// Inputs: [state, struct_ptr]
    /// Outputs: [new_state, value]
    StructFieldLoad { field: FieldId },

    /// Store struct field
    /// Inputs: [state, struct_ptr, value]
    /// Outputs: [new_state]
    StructFieldStore { field: FieldId },

    // ===== Region-specific Nodes =====
    /// Region parameter (input to a region)
    RegionParam { index: usize },

    /// Region result (output from a region)
    /// Inputs: [value]
    RegionResult,
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
    pub fn new(types: &'a TypeArena, interner: SharedInterner) -> Self {
        Self {
            functions: Vec::new(),
            extern_functions: Vec::new(),
            types,
            interner,
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
        self.regions
            .get(id.0)
            .unwrap_or_else(|| panic!("Invalid RegionId({}) in function", id.0))
    }

    /// Get a mutable region by ID
    #[inline]
    pub fn region_mut(&mut self, id: RegionId) -> &mut Region {
        self.regions
            .get_mut(id.0)
            .unwrap_or_else(|| panic!("Invalid RegionId({}) in function", id.0))
    }
}

// ===== Hash-Consing Support =====

/// Key for hash-consing pure operations
/// Two nodes are equivalent if they have the same kind, inputs, and output types
#[derive(Hash, Eq, PartialEq, Clone)]
pub(crate) struct NodeKey {
    pub kind: NodeKeyKind,
    pub inputs: Vec<ValueId>,
    pub output_types: Vec<TypeId>,
}

/// Simplified node kind for hash-consing (only pure operations)
#[derive(Hash, Eq, PartialEq, Clone)]
pub(crate) enum NodeKeyKind {
    Const(ConstValue), // ConstValue includes String which is hashable
    Binary { op: BinaryOp },
    Unary { op: UnaryOp },
    StructFieldAddr { field: FieldId },
}
