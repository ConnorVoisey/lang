//! Builder for constructing RVSDG graphs efficiently

use super::*;
use crate::lexer::Span;
use rustc_hash::FxHashMap;

pub struct FunctionBuilder {
    func: Function,
    next_region_id: usize,

    // Track regions and their contents
    regions: Vec<Region>,

    // Current region being built
    current_region: Option<RegionId>,

    // Stack of parent regions (for nested regions like gamma/theta)
    region_stack: Vec<Option<RegionId>>,

    // Map AST symbols to RVSDG values for the current scope
    symbol_map: Vec<FxHashMap<SymbolId, ValueId>>,

    // Hash-consing cache for pure operations (CSE)
    value_cache: FxHashMap<NodeKey, NodeId>,
}

pub struct RegionBuilder<'a> {
    fb: &'a mut FunctionBuilder,
    region_id: RegionId,
}

impl FunctionBuilder {
    pub fn new(
        id: FunctionId,
        name: SymbolId,
        params: Vec<Parameter>,
        return_type: TypeId,
        span: Span,
    ) -> Self {
        Self {
            func: Function {
                id,
                name,
                params,
                return_type,
                root: NodeId(0), // Will be set when lambda is created
                span,
                nodes: Vec::new(),
                regions: Vec::new(), // Will be populated by finish()
                is_exported: false,
                inline_hint: InlineHint::Auto,
            },
            next_region_id: 0,
            regions: Vec::new(),
            current_region: None,
            region_stack: Vec::new(),
            symbol_map: vec![FxHashMap::default()],
            value_cache: FxHashMap::default(),
        }
    }

    pub fn set_exported(&mut self, exported: bool) {
        self.func.is_exported = exported;
    }

    pub fn set_inline_hint(&mut self, hint: InlineHint) {
        self.func.inline_hint = hint;
    }

    // ===== Node Creation =====

    fn alloc_node(
        &mut self,
        kind: NodeKind,
        output_types: Vec<TypeId>,
        inputs: Vec<ValueId>,
        span: Span,
    ) -> NodeId {
        let id = NodeId(self.func.nodes.len());
        self.func.nodes.push(Node {
            id,
            kind,
            span,
            output_types,
            inputs,
        });

        // Add to current region if one is active
        if let Some(region_id) = self.current_region {
            self.regions[region_id.0].nodes.push(id);
        }

        id
    }

    /// Create a value from a node with a single output
    fn value(&self, node: NodeId) -> ValueId {
        ValueId {
            node,
            output_index: 0,
        }
    }

    /// Create a value from a node with multiple outputs
    fn value_n(&self, node: NodeId, index: u32) -> ValueId {
        ValueId {
            node,
            output_index: index,
        }
    }

    // ===== State Token =====

    pub fn state_token(&mut self, ty: TypeId, span: Span) -> ValueId {
        let node = self.alloc_node(NodeKind::StateToken, vec![ty], vec![], span);
        self.value(node)
    }

    // ===== Constant Nodes =====

    pub fn const_i64(&mut self, value: i64, ty: TypeId, span: Span) -> ValueId {
        // Check cache
        let key = NodeKey {
            kind: NodeKeyKind::Const(ConstValue::I64(value)),
            inputs: vec![],
            output_types: vec![ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Create new node
        let node = self.alloc_node(
            NodeKind::Const {
                value: ConstValue::I64(value),
            },
            vec![ty],
            vec![],
            span,
        );

        // Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    pub fn const_u64(&mut self, value: u64, ty: TypeId, span: Span) -> ValueId {
        // Check cache
        let key = NodeKey {
            kind: NodeKeyKind::Const(ConstValue::U64(value)),
            inputs: vec![],
            output_types: vec![ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Create new node
        let node = self.alloc_node(
            NodeKind::Const {
                value: ConstValue::U64(value),
            },
            vec![ty],
            vec![],
            span,
        );

        // Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    pub fn const_bool(&mut self, value: bool, ty: TypeId, span: Span) -> ValueId {
        // Check cache
        let key = NodeKey {
            kind: NodeKeyKind::Const(ConstValue::Bool(value)),
            inputs: vec![],
            output_types: vec![ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Create new node
        let node = self.alloc_node(
            NodeKind::Const {
                value: ConstValue::Bool(value),
            },
            vec![ty],
            vec![],
            span,
        );

        // Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    pub fn const_string(&mut self, data: Vec<u8>, ty: TypeId, span: Span) -> ValueId {
        // Check cache - hash-consing will deduplicate identical strings
        let key = NodeKey {
            kind: NodeKeyKind::Const(ConstValue::String(data.clone())),
            inputs: vec![],
            output_types: vec![ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Create new node
        let node = self.alloc_node(
            NodeKind::Const {
                value: ConstValue::String(data),
            },
            vec![ty],
            vec![],
            span,
        );

        // Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    // ===== Arithmetic Operations =====

    pub fn binary(
        &mut self,
        op: BinaryOp,
        mut lhs: ValueId,
        mut rhs: ValueId,
        result_ty: TypeId,
        span: Span,
    ) -> ValueId {
        // Step 1: Try constant folding
        if let Some(folded) = self.try_fold_binary(op, lhs, rhs, result_ty, span.clone()) {
            return folded;
        }

        // Step 2: Canonicalize commutative operations
        if op.is_commutative() && rhs < lhs {
            std::mem::swap(&mut lhs, &mut rhs);
        }

        // Step 3: Check cache
        let key = NodeKey {
            kind: NodeKeyKind::Binary { op },
            inputs: vec![lhs, rhs],
            output_types: vec![result_ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Step 4: Create new node
        let node = self.alloc_node(
            NodeKind::Binary { op },
            vec![result_ty],
            vec![lhs, rhs],
            span,
        );

        // Step 5: Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    pub fn unary(
        &mut self,
        op: UnaryOp,
        operand: ValueId,
        result_ty: TypeId,
        span: Span,
    ) -> ValueId {
        // Step 1: Try constant folding
        if let Some(folded) = self.try_fold_unary(op, operand, result_ty, span.clone()) {
            return folded;
        }

        // Step 2: Check cache
        let key = NodeKey {
            kind: NodeKeyKind::Unary { op },
            inputs: vec![operand],
            output_types: vec![result_ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Step 3: Create new node
        let node = self.alloc_node(NodeKind::Unary { op }, vec![result_ty], vec![operand], span);

        // Step 4: Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    // ===== Memory Operations =====

    pub fn alloc(&mut self, state: ValueId, ty: TypeId, span: Span) -> (ValueId, ValueId) {
        let node = self.alloc_node(
            NodeKind::Alloc { ty },
            vec![ty, ty], // [new_state, pointer]
            vec![state],
            span,
        );
        (self.value_n(node, 0), self.value_n(node, 1))
    }

    pub fn load(
        &mut self,
        state: ValueId,
        addr: ValueId,
        ty: TypeId,
        span: Span,
    ) -> (ValueId, ValueId) {
        let state_ty = ty; // State type is same as loaded type for simplicity
        let node = self.alloc_node(
            NodeKind::Load { ty },
            vec![state_ty, ty], // [new_state, value]
            vec![state, addr],
            span,
        );
        (self.value_n(node, 0), self.value_n(node, 1))
    }

    pub fn store(
        &mut self,
        state: ValueId,
        addr: ValueId,
        value: ValueId,
        ty: TypeId,
        span: Span,
    ) -> ValueId {
        let node = self.alloc_node(
            NodeKind::Store { ty },
            vec![ty], // [new_state]
            vec![state, addr, value],
            span,
        );
        self.value(node)
    }

    // ===== Call =====

    pub fn call(
        &mut self,
        state: ValueId,
        function: FunctionId,
        args: Vec<ValueId>,
        return_ty: TypeId,
        span: Span,
    ) -> (ValueId, ValueId) {
        let mut inputs = vec![state];
        inputs.extend(args);

        let node = self.alloc_node(
            NodeKind::Call { function },
            vec![return_ty, return_ty], // [new_state, result]
            inputs,
            span,
        );
        (self.value_n(node, 0), self.value_n(node, 1))
    }

    // ===== Struct Operations =====

    pub fn struct_field_addr(
        &mut self,
        struct_ptr: ValueId,
        field: FieldId,
        field_ty: TypeId,
        span: Span,
    ) -> ValueId {
        // Check cache (pure address calculation)
        let key = NodeKey {
            kind: NodeKeyKind::StructFieldAddr { field },
            inputs: vec![struct_ptr],
            output_types: vec![field_ty],
        };

        if let Some(&cached_node) = self.value_cache.get(&key) {
            return ValueId::from_node(cached_node);
        }

        // Create new node
        let node = self.alloc_node(
            NodeKind::StructFieldAddr { field },
            vec![field_ty],
            vec![struct_ptr],
            span,
        );

        // Cache it
        self.value_cache.insert(key, node);
        self.value(node)
    }

    pub fn struct_field_load(
        &mut self,
        state: ValueId,
        struct_ptr: ValueId,
        field: FieldId,
        field_ty: TypeId,
        span: Span,
    ) -> (ValueId, ValueId) {
        let node = self.alloc_node(
            NodeKind::StructFieldLoad { field },
            vec![field_ty, field_ty], // [new_state, value]
            vec![state, struct_ptr],
            span,
        );
        (self.value_n(node, 0), self.value_n(node, 1))
    }

    pub fn struct_field_store(
        &mut self,
        state: ValueId,
        struct_ptr: ValueId,
        field: FieldId,
        value: ValueId,
        state_ty: TypeId,
        span: Span,
    ) -> ValueId {
        let node = self.alloc_node(
            NodeKind::StructFieldStore { field },
            vec![state_ty], // [new_state]
            vec![state, struct_ptr, value],
            span,
        );
        self.value(node)
    }

    // ===== Region Management =====

    fn new_region(&mut self) -> RegionId {
        let id = RegionId(self.next_region_id);
        self.next_region_id += 1;

        self.regions.push(Region {
            id,
            params: Vec::new(),
            results: Vec::new(),
            nodes: Vec::new(),
        });

        id
    }

    pub fn start_region(&mut self, region_id: RegionId) {
        // Save the current region to the stack before entering new region
        self.region_stack.push(self.current_region);
        self.current_region = Some(region_id);
        // Push new scope for symbols
        self.symbol_map.push(FxHashMap::default());
    }

    pub fn end_region(&mut self) {
        // Restore the parent region from the stack
        self.current_region = self.region_stack.pop().expect("Region stack underflow");
        // Pop scope
        self.symbol_map.pop();
    }

    pub fn region_param(
        &mut self,
        region_id: RegionId,
        index: usize,
        ty: TypeId,
        span: Span,
    ) -> ValueId {
        let node = self.alloc_node(NodeKind::RegionParam { index }, vec![ty], vec![], span);
        // Add to region's params
        self.regions[region_id.0].params.push(node);
        self.value(node)
    }

    pub fn region_result(&mut self, value: ValueId, span: Span) -> NodeId {
        let ty = value.node; // Placeholder - we'd need to track types properly
        let node = self.alloc_node(NodeKind::RegionResult, vec![], vec![value], span);

        // Add to current region's results
        if let Some(region_id) = self.current_region {
            self.regions[region_id.0].results.push(node);
        }

        node
    }

    // ===== Structural Nodes =====

    pub fn create_gamma(
        &mut self,
        condition: ValueId,
        captured: Vec<ValueId>,
        output_types: Vec<TypeId>,
        span: Span,
    ) -> (NodeId, Vec<RegionId>) {
        // Create regions for true and false branches
        let true_region = self.new_region();
        let false_region = self.new_region();

        // Create region parameters for captured values with their actual types
        // We need to get the types of the captured values from the nodes
        for (i, &captured_val) in captured.iter().enumerate() {
            let captured_node = &self.func.nodes[captured_val.node.0];
            let captured_ty = captured_node.output_types[captured_val.output_index as usize];

            // Create param for true region
            let _true_param = self.alloc_node(
                NodeKind::RegionParam { index: i },
                vec![captured_ty],
                vec![],
                span.clone(),
            );
            self.regions[true_region.0].params.push(_true_param);

            // Create param for false region
            let _false_param = self.alloc_node(
                NodeKind::RegionParam { index: i },
                vec![captured_ty],
                vec![],
                span.clone(),
            );
            self.regions[false_region.0].params.push(_false_param);
        }

        let regions = vec![true_region, false_region];

        let mut inputs = vec![condition];
        inputs.extend(captured);

        let node = self.alloc_node(
            NodeKind::Gamma {
                regions: regions.clone(),
            },
            output_types,
            inputs,
            span,
        );

        (node, regions)
    }

    pub fn create_theta(
        &mut self,
        initial_values: Vec<ValueId>,
        output_types: Vec<TypeId>,
        span: Span,
    ) -> (NodeId, RegionId) {
        let region = self.new_region();

        // Create region parameters for loop-carried values with their actual types
        for (i, &initial_val) in initial_values.iter().enumerate() {
            let initial_node = &self.func.nodes[initial_val.node.0];
            let initial_ty = initial_node.output_types[initial_val.output_index as usize];

            let param = self.alloc_node(
                NodeKind::RegionParam { index: i },
                vec![initial_ty],
                vec![],
                span.clone(),
            );
            self.regions[region.0].params.push(param);
        }

        let node = self.alloc_node(
            NodeKind::Theta { region },
            output_types,
            initial_values,
            span,
        );

        (node, region)
    }

    pub fn create_lambda(&mut self, return_ty: TypeId, span: Span) -> RegionId {
        let region = self.new_region();

        let param_types: Vec<TypeId> = self.func.params.iter().map(|p| p.ty).collect();

        // Create region parameters for function parameters
        for (i, param_ty) in param_types.iter().enumerate() {
            let param_node = self.alloc_node(
                NodeKind::RegionParam { index: i },
                vec![*param_ty],
                vec![],
                span.clone(),
            );
            self.regions[region.0].params.push(param_node);
        }

        let node = self.alloc_node(NodeKind::Lambda { region }, vec![return_ty], vec![], span);

        self.func.root = node;
        region
    }

    // ===== Symbol Mapping =====

    pub fn define_symbol(&mut self, symbol_id: SymbolId, value: ValueId) {
        if let Some(scope) = self.symbol_map.last_mut() {
            scope.insert(symbol_id, value);
        }
    }

    pub fn lookup_symbol(&self, symbol_id: SymbolId) -> Option<ValueId> {
        // Search from innermost to outermost scope
        for scope in self.symbol_map.iter().rev() {
            if let Some(&value) = scope.get(&symbol_id) {
                return Some(value);
            }
        }
        None
    }

    // ===== Hash-Consing Helpers =====

    /// Extract constant value from a ValueId (if it's a constant)
    fn get_const_value(&self, value_id: ValueId) -> Option<&ConstValue> {
        // Constants only have one output
        if value_id.output_index != 0 {
            return None;
        }
        let node = &self.func.nodes[value_id.node.0];
        match &node.kind {
            NodeKind::Const { value } => Some(value),
            _ => None,
        }
    }

    /// Try to fold a binary operation on constants
    fn try_fold_binary(
        &mut self,
        op: BinaryOp,
        lhs: ValueId,
        rhs: ValueId,
        result_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        let lhs_val = self.get_const_value(lhs)?;
        let rhs_val = self.get_const_value(rhs)?;

        let result = match (lhs_val, rhs_val) {
            (ConstValue::I64(a), ConstValue::I64(b)) => match op {
                BinaryOp::Add => ConstValue::I64(a.wrapping_add(*b)),
                BinaryOp::Sub => ConstValue::I64(a.wrapping_sub(*b)),
                BinaryOp::Mul => ConstValue::I64(a.wrapping_mul(*b)),
                BinaryOp::Div => ConstValue::I64(a.checked_div(*b)?),
                BinaryOp::Rem => ConstValue::I64(a.checked_rem(*b)?),
                BinaryOp::Lt => ConstValue::Bool(a < b),
                BinaryOp::Le => ConstValue::Bool(a <= b),
                BinaryOp::Gt => ConstValue::Bool(a > b),
                BinaryOp::Ge => ConstValue::Bool(a >= b),
                BinaryOp::Eq => ConstValue::Bool(a == b),
                BinaryOp::Ne => ConstValue::Bool(a != b),
                _ => return None,
            },
            (ConstValue::U64(a), ConstValue::U64(b)) => match op {
                BinaryOp::Add => ConstValue::U64(a.wrapping_add(*b)),
                BinaryOp::Sub => ConstValue::U64(a.wrapping_sub(*b)),
                BinaryOp::Mul => ConstValue::U64(a.wrapping_mul(*b)),
                BinaryOp::Div => ConstValue::U64(a.checked_div(*b)?),
                BinaryOp::Rem => ConstValue::U64(a.checked_rem(*b)?),
                BinaryOp::Lt => ConstValue::Bool(a < b),
                BinaryOp::Le => ConstValue::Bool(a <= b),
                BinaryOp::Gt => ConstValue::Bool(a > b),
                BinaryOp::Ge => ConstValue::Bool(a >= b),
                BinaryOp::Eq => ConstValue::Bool(a == b),
                BinaryOp::Ne => ConstValue::Bool(a != b),
                _ => return None,
            },
            (ConstValue::Bool(a), ConstValue::Bool(b)) => match op {
                BinaryOp::And => ConstValue::Bool(*a && *b),
                BinaryOp::Or => ConstValue::Bool(*a || *b),
                BinaryOp::Eq => ConstValue::Bool(a == b),
                BinaryOp::Ne => ConstValue::Bool(a != b),
                _ => return None,
            },
            _ => return None, // Type mismatch
        };

        // Create folded constant (will be cached)
        Some(match result {
            ConstValue::I64(v) => self.const_i64(v, result_ty, span),
            ConstValue::U64(v) => self.const_u64(v, result_ty, span),
            ConstValue::Bool(v) => self.const_bool(v, result_ty, span),
            ConstValue::String(_) => unreachable!("String constants cannot be folded"),
        })
    }

    /// Try to fold a unary operation on a constant
    fn try_fold_unary(
        &mut self,
        op: UnaryOp,
        operand: ValueId,
        result_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        let operand_val = self.get_const_value(operand)?;

        let result = match (operand_val, op) {
            (ConstValue::I64(v), UnaryOp::Neg) => ConstValue::I64(v.wrapping_neg()),
            (ConstValue::U64(v), UnaryOp::Neg) => ConstValue::U64(v.wrapping_neg()),
            (ConstValue::Bool(v), UnaryOp::Not) => ConstValue::Bool(!v),
            _ => return None, // Type mismatch
        };

        // Create folded constant (will be cached)
        Some(match result {
            ConstValue::I64(v) => self.const_i64(v, result_ty, span),
            ConstValue::U64(v) => self.const_u64(v, result_ty, span),
            ConstValue::Bool(v) => self.const_bool(v, result_ty, span),
            ConstValue::String(_) => unreachable!("String constants cannot be folded"),
        })
    }

    // ===== Finalization =====

    /// Get a region by ID
    pub fn get_region(&self, id: RegionId) -> &Region {
        &self.regions[id.0]
    }

    /// Get a node by ID
    pub fn get_node(&self, id: NodeId) -> &Node {
        &self.func.nodes[id.0]
    }

    /// Get the type of a value
    pub fn get_value_type(&self, value: ValueId) -> Option<TypeId> {
        let node = &self.func.nodes[value.node.0];
        node.output_types.get(value.output_index as usize).copied()
    }

    pub fn finish(mut self) -> Function {
        // Move regions into function before returning
        self.func.regions = self.regions;
        self.func
    }
}
