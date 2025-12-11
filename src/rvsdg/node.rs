//! Utilities and helpers for RVSDG nodes

use super::*;

impl Node {
    /// Check if this node is a structural node (contains regions)
    pub fn is_structural(&self) -> bool {
        matches!(
            self.kind,
            NodeKind::Lambda { .. } | NodeKind::Gamma { .. } | NodeKind::Theta { .. }
        )
    }

    /// Check if this node is a simple value node
    pub fn is_simple(&self) -> bool {
        !self.is_structural()
    }

    /// Get the number of outputs this node produces
    pub fn num_outputs(&self) -> usize {
        self.output_types.len()
    }

    /// Check if this node has side effects (memory operations)
    pub fn has_side_effects(&self) -> bool {
        matches!(self.kind, NodeKind::Store { .. } | NodeKind::Call { .. })
    }

    /// Check if this node is a memory operation
    pub fn is_memory_op(&self) -> bool {
        matches!(
            self.kind,
            NodeKind::Alloc { .. } | NodeKind::Load { .. } | NodeKind::Store { .. }
        )
    }
}

impl ValueId {
    /// Create a new ValueId from a node with output index 0
    pub fn from_node(node: NodeId) -> Self {
        Self {
            node,
            output_index: 0,
        }
    }

    /// Create a new ValueId from a node with a specific output index
    pub fn from_node_output(node: NodeId, output_index: u32) -> Self {
        Self { node, output_index }
    }
}

impl Region {
    /// Check if this region is empty
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Get the number of nodes in this region
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }
}

impl BinaryOp {
    /// Check if this is an arithmetic operation
    pub fn is_arithmetic(&self) -> bool {
        matches!(
            self,
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem
        )
    }

    /// Check if this is a comparison operation
    pub fn is_comparison(&self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }

    /// Check if this is a logical operation
    pub fn is_logical(&self) -> bool {
        matches!(self, Self::And | Self::Or)
    }

    /// Check if this operation is commutative
    pub fn is_commutative(&self) -> bool {
        matches!(
            self,
            Self::Add | Self::Mul | Self::Eq | Self::Ne | Self::And | Self::Or
        )
    }
}
