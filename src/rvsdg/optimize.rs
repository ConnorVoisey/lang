//! RVSDG optimization passes
//!
//! This module contains optimization passes that operate on the RVSDG IR.
//! Optimizations are designed to be fast single-pass algorithms that maintain
//! the structural properties of RVSDG.

use super::*;
use rustc_hash::FxHashSet;

/// Run dead code elimination on a function
///
/// Uses mark-and-sweep algorithm:
/// 1. Mark all nodes reachable from RegionResults and nodes with observable effects
/// 2. Sweep unmarked nodes from all regions
#[tracing::instrument(skip(func))]
pub fn dead_code_elimination(func: &mut Function) {
    let live_nodes = mark_live_nodes(func);
    sweep_dead_nodes(func, &live_nodes);
}

/// Mark phase: collect all live nodes
fn mark_live_nodes(func: &Function) -> FxHashSet<NodeId> {
    let mut live = FxHashSet::default();

    // Mark from all regions in the function
    for region in &func.regions {
        // All RegionResult nodes are live (they produce region outputs)
        for &result_node_id in &region.results {
            mark_node(func, result_node_id, &mut live);
        }

        // Mark nodes with observable effects
        for &node_id in &region.nodes {
            let node = func.node(node_id);
            if has_observable_effects(&node.kind) {
                mark_node(func, node_id, &mut live);
            }
        }
    }

    // Mark structural nodes (Lambda, Gamma, Theta) as they define control flow
    for node in &func.nodes {
        match &node.kind {
            NodeKind::Lambda { .. } | NodeKind::Gamma { .. } | NodeKind::Theta { .. } => {
                mark_node(func, node.id, &mut live);
            }
            _ => {}
        }
    }

    live
}

/// Recursively mark a node and all its inputs as live
fn mark_node(func: &Function, node_id: NodeId, live: &mut FxHashSet<NodeId>) {
    // If already marked, skip
    if !live.insert(node_id) {
        return;
    }

    let node = func.node(node_id);

    // Mark all input nodes
    for input in &node.inputs {
        mark_node(func, input.node, live);
    }

    // For structural nodes, mark nodes in their regions
    match &node.kind {
        NodeKind::Lambda { region } => {
            mark_region(func, *region, live);
        }
        NodeKind::Gamma { regions } => {
            for &region_id in regions {
                mark_region(func, region_id, live);
            }
        }
        NodeKind::Theta { region } => {
            mark_region(func, *region, live);
        }
        _ => {}
    }
}

/// Mark all nodes in a region
fn mark_region(func: &Function, region_id: RegionId, live: &mut FxHashSet<NodeId>) {
    let region = func.region(region_id);

    // Mark all region parameters
    for &param_node_id in &region.params {
        mark_node(func, param_node_id, live);
    }

    // Mark all result nodes (these define what the region produces)
    for &result_node_id in &region.results {
        mark_node(func, result_node_id, live);
    }

    // Mark all nodes in the region
    for &node_id in &region.nodes {
        let node = func.node(node_id);
        // Only mark if it's a result, has effects, or is structural
        if matches!(node.kind, NodeKind::RegionResult) || has_observable_effects(&node.kind) {
            mark_node(func, node_id, live);
        }
    }
}

/// Check if a node has observable effects (can't be eliminated even if unused)
fn has_observable_effects(kind: &NodeKind) -> bool {
    match kind {
        // All function calls have effects (even if we don't use return value)
        NodeKind::Call { .. } => true,

        // Memory operations have effects
        NodeKind::Store { .. } => true,

        // Alloc could have effects depending on implementation
        // For now, treat as effectful to be safe
        NodeKind::Alloc { .. } => true,

        // Load operations have effects (they depend on state)
        NodeKind::Load { .. } => true,

        // State token is effectful
        NodeKind::StateToken => true,

        // RegionResult produces output
        NodeKind::RegionResult => true,

        // Everything else is pure
        _ => false,
    }
}

/// Sweep phase: remove dead nodes from regions
fn sweep_dead_nodes(func: &mut Function, live: &FxHashSet<NodeId>) {
    // Remove dead nodes from each region's node list
    for region in &mut func.regions {
        region.nodes.retain(|&node_id| live.contains(&node_id));
    }

    // Note: We don't remove nodes from func.nodes array to keep NodeId indices stable
    // Dead nodes remain in the array but are unreachable from any region
    // This is fine because we never iterate func.nodes directly in code generation
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dce_removes_unused_const() {
        // Create a simple function with an unused constant
        // This would need a proper test setup with Function/Module construction
        // For now, this is a placeholder for future tests
    }
}
