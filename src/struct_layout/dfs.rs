use crate::types::StructId;
use rustc_hash::FxHashSet;

#[derive(Debug, PartialEq)]
pub enum TopologicalSortResult {
    Success(Vec<StructId>),
    Cycle {
        sorted: Vec<StructId>,
        cycle_nodes: Vec<StructId>,
    },
}

#[derive(Debug)]
pub struct StructWithChild {
    pub struct_id: StructId,
    pub child_ids: FxHashSet<StructId>,
}

#[derive(Clone, Copy, PartialEq)]
enum StructState {
    Unvisited,
    Visiting,
    Visited,
}

pub fn topological_sort_rev(structs: &[StructWithChild]) -> TopologicalSortResult {
    if structs.is_empty() {
        return TopologicalSortResult::Success(Vec::new());
    }

    let max_id = structs.iter().map(|s| s.struct_id.0).max().unwrap();
    let mut states = vec![StructState::Unvisited; max_id + 1];
    let mut result = Vec::with_capacity(structs.len());
    let mut cycle_nodes = FxHashSet::default();
    let mut has_cycle = false;
    let mut recursion_stack = Vec::new();

    fn dfs(
        struct_id: StructId,
        structs: &[StructWithChild],
        states: &mut [StructState],
        result: &mut Vec<StructId>,
        cycle_nodes: &mut FxHashSet<StructId>,
        has_cycle: &mut bool,
        recursion_stack: &mut Vec<StructId>,
    ) -> bool {
        match states[struct_id.0] {
            StructState::Visited => return false,
            StructState::Visiting => {
                // Cycle detected - mark all nodes in recursion stack from this node onwards
                *has_cycle = true;
                let mut found_cycle_start = false;
                for &stack_node in recursion_stack.iter() {
                    if stack_node == struct_id {
                        found_cycle_start = true;
                    }
                    if found_cycle_start {
                        cycle_nodes.insert(stack_node);
                    }
                }
                cycle_nodes.insert(struct_id);
                return true;
            }
            StructState::Unvisited => {}
        }

        states[struct_id.0] = StructState::Visiting;
        recursion_stack.push(struct_id);

        let mut is_part_of_cycle = false;

        // Visit all children
        if let Some(struct_data) = structs.iter().find(|s| s.struct_id == struct_id) {
            for &child_id in &struct_data.child_ids {
                let child_in_cycle = dfs(
                    child_id,
                    structs,
                    states,
                    result,
                    cycle_nodes,
                    has_cycle,
                    recursion_stack,
                );

                // If the child is part of a cycle and we're still on the recursion stack,
                // check if we're part of the cycle too
                if child_in_cycle && cycle_nodes.contains(&struct_id) {
                    is_part_of_cycle = true;
                }
            }
        }

        recursion_stack.pop();
        states[struct_id.0] = StructState::Visited;

        // Only add to result if not part of a cycle
        if !cycle_nodes.contains(&struct_id) {
            result.push(struct_id);
        }

        is_part_of_cycle || cycle_nodes.contains(&struct_id)
    }

    // Visit all nodes
    for struct_data in structs {
        if states[struct_data.struct_id.0] == StructState::Unvisited {
            dfs(
                struct_data.struct_id,
                structs,
                &mut states,
                &mut result,
                &mut cycle_nodes,
                &mut has_cycle,
                &mut recursion_stack,
            );
        }
    }

    if has_cycle {
        let cycle_vec: Vec<StructId> = cycle_nodes.into_iter().collect();
        TopologicalSortResult::Cycle {
            sorted: result,
            cycle_nodes: cycle_vec,
        }
    } else {
        TopologicalSortResult::Success(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    // Helper function to create a test StructWithChild with minimal boilerplate
    fn make_struct(id: usize, children: &[usize]) -> StructWithChild {
        let mut child_ids = FxHashSet::default();
        for &child_id in children {
            child_ids.insert(StructId(child_id));
        }

        StructWithChild {
            struct_id: StructId(id),
            child_ids,
        }
    }

    #[test]
    fn empty_graph() {
        let nodes = [];
        let result = topological_sort_rev(&nodes);
        assert_eq!(result, TopologicalSortResult::Success(vec![]));
    }

    #[test]
    fn single_node() {
        let nodes = [make_struct(0, &[])];
        let result = topological_sort_rev(&nodes);
        assert_eq!(result, TopologicalSortResult::Success(vec![StructId(0)]));
    }

    #[test]
    fn independent_nodes() {
        // Multiple nodes with no dependencies
        let nodes = [
            make_struct(0, &[]),
            make_struct(1, &[]),
            make_struct(2, &[]),
        ];

        let result = topological_sort_rev(&nodes);
        // All nodes should be in result, order doesn't matter for independent nodes
        match result {
            TopologicalSortResult::Success(sorted) => {
                assert_eq!(sorted.len(), 3);
                assert!(sorted.contains(&StructId(0)));
                assert!(sorted.contains(&StructId(1)));
                assert!(sorted.contains(&StructId(2)));
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn linear_chain() {
        // 0 -> 1 -> 2 -> 3 (0 contains 1, 1 contains 2, etc.)
        // For struct layout, we need to compute 3 first (no children), then 2, then 1, then 0
        let nodes = [
            make_struct(0, &[1]),
            make_struct(1, &[2]),
            make_struct(2, &[3]),
            make_struct(3, &[]),
        ];

        let result = topological_sort_rev(&nodes);
        assert_eq!(
            result,
            TopologicalSortResult::Success(vec![
                StructId(3),
                StructId(2),
                StructId(1),
                StructId(0)
            ])
        );
    }

    #[test]
    fn diamond_pattern() {
        // Classic diamond: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        // For struct layout: 3 must be computed before 1 and 2, which must be computed before 0
        let nodes = [
            make_struct(0, &[1, 2]),
            make_struct(1, &[3]),
            make_struct(2, &[3]),
            make_struct(3, &[]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Success(sorted) => {
                // Verify all nodes are present
                assert_eq!(sorted.len(), 4);

                // Verify topological ordering constraints (children before parents)
                let pos: std::collections::HashMap<_, _> =
                    sorted.iter().enumerate().map(|(i, &id)| (id, i)).collect();

                // Node 3 must come before 1 and 2 (children before parents)
                assert!(pos[&StructId(3)] < pos[&StructId(1)]);
                assert!(pos[&StructId(3)] < pos[&StructId(2)]);

                // Nodes 1 and 2 must come before 0
                assert!(pos[&StructId(1)] < pos[&StructId(0)]);
                assert!(pos[&StructId(2)] < pos[&StructId(0)]);
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn complex_dag() {
        // More complex DAG with multiple paths
        //     0
        //    / \
        //   1   2
        //   |\ /|
        //   | X |
        //   |/ \|
        //   3   4
        //    \ /
        //     5
        // For struct layout: 5 first, then 3 and 4, then 1 and 2, then 0
        let nodes = [
            make_struct(0, &[1, 2]),
            make_struct(1, &[3, 4]),
            make_struct(2, &[3, 4]),
            make_struct(3, &[5]),
            make_struct(4, &[5]),
            make_struct(5, &[]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Success(sorted) => {
                // Verify all nodes are present
                assert_eq!(sorted.len(), 6);

                // Verify topological ordering constraints (children before parents)
                let pos: std::collections::HashMap<_, _> =
                    sorted.iter().enumerate().map(|(i, &id)| (id, i)).collect();

                // Node 5 must come before 3 and 4
                assert!(pos[&StructId(5)] < pos[&StructId(3)]);
                assert!(pos[&StructId(5)] < pos[&StructId(4)]);

                // Nodes 3 and 4 must come before 1 and 2
                assert!(pos[&StructId(3)] < pos[&StructId(1)]);
                assert!(pos[&StructId(4)] < pos[&StructId(1)]);
                assert!(pos[&StructId(3)] < pos[&StructId(2)]);
                assert!(pos[&StructId(4)] < pos[&StructId(2)]);

                // Nodes 1 and 2 must come before 0
                assert!(pos[&StructId(1)] < pos[&StructId(0)]);
                assert!(pos[&StructId(2)] < pos[&StructId(0)]);
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn multiple_roots() {
        // Graph with multiple starting points
        //   0 -> 2
        //   1 -> 2
        //   2 -> 3
        // For struct layout: 3 first, then 2, then 0 and 1
        let nodes = [
            make_struct(0, &[2]),
            make_struct(1, &[2]),
            make_struct(2, &[3]),
            make_struct(3, &[]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Success(sorted) => {
                // Verify all nodes are present
                assert_eq!(sorted.len(), 4);

                // Verify constraints (children before parents)
                let pos: std::collections::HashMap<_, _> =
                    sorted.iter().enumerate().map(|(i, &id)| (id, i)).collect();

                assert!(pos[&StructId(3)] < pos[&StructId(2)]);
                assert!(pos[&StructId(2)] < pos[&StructId(0)]);
                assert!(pos[&StructId(2)] < pos[&StructId(1)]);
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn simple_cycle() {
        // Simple cycle: 0 -> 1 -> 2 -> 0
        let nodes = [
            make_struct(0, &[1]),
            make_struct(1, &[2]),
            make_struct(2, &[0]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Cycle {
                sorted,
                cycle_nodes,
            } => {
                assert_eq!(sorted.len(), 0);
                assert_eq!(cycle_nodes.len(), 3);
                assert!(cycle_nodes.contains(&StructId(0)));
                assert!(cycle_nodes.contains(&StructId(1)));
                assert!(cycle_nodes.contains(&StructId(2)));
            }
            _ => panic!("Expected cycle detection"),
        }
    }

    #[test]
    fn self_loop() {
        // Node points to itself
        let nodes = [make_struct(0, &[0])];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Cycle {
                sorted,
                cycle_nodes,
            } => {
                assert_eq!(sorted.len(), 0);
                assert!(cycle_nodes.contains(&StructId(0)));
            }
            _ => panic!("Expected cycle detection"),
        }
    }

    #[test]
    fn cycle_with_independent_nodes() {
        // Mix of cycle and valid nodes
        // 0 and 1 are independent
        // 2 -> 3 -> 4 -> 2 (cycle)
        let nodes = [
            make_struct(0, &[]),
            make_struct(1, &[]),
            make_struct(2, &[3]),
            make_struct(3, &[4]),
            make_struct(4, &[2]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Cycle {
                sorted,
                cycle_nodes,
            } => {
                // Independent nodes should be sorted
                assert_eq!(sorted.len(), 2);
                assert!(sorted.contains(&StructId(0)));
                assert!(sorted.contains(&StructId(1)));

                // Cycle nodes should be identified
                assert_eq!(cycle_nodes.len(), 3);
                assert!(cycle_nodes.contains(&StructId(2)));
                assert!(cycle_nodes.contains(&StructId(3)));
                assert!(cycle_nodes.contains(&StructId(4)));
            }
            _ => panic!("Expected cycle detection"),
        }
    }

    #[test]
    fn dag_with_back_references() {
        // Test case where nodes reference earlier nodes but no cycles
        // 0 -> 1 -> 3
        // 0 -> 2 -> 3
        // For struct layout: 3 first, then 1 and 2, then 0
        let nodes = [
            make_struct(0, &[1, 2]),
            make_struct(1, &[3]),
            make_struct(2, &[3]),
            make_struct(3, &[]),
        ];

        let result = topological_sort_rev(&nodes);
        match result {
            TopologicalSortResult::Success(sorted) => {
                assert_eq!(sorted.len(), 4);
                let pos: std::collections::HashMap<_, _> =
                    sorted.iter().enumerate().map(|(i, &id)| (id, i)).collect();
                assert!(pos[&StructId(3)] < pos[&StructId(1)]);
                assert!(pos[&StructId(3)] < pos[&StructId(2)]);
                assert!(pos[&StructId(1)] < pos[&StructId(0)]);
                assert!(pos[&StructId(2)] < pos[&StructId(0)]);
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn partial_cycle() {
        // 0 -> 1 -> 2
        //      ^    |
        //      |    v
        //      4 <- 3
        // So 0 is independent, 1->2->3->4->1 is a cycle
        let nodes = [
            make_struct(0, &[1]),
            make_struct(1, &[2]),
            make_struct(2, &[3]),
            make_struct(3, &[4]),
            make_struct(4, &[1]),
        ];

        let result = topological_sort_rev(&nodes);

        match result {
            TopologicalSortResult::Cycle {
                sorted,
                cycle_nodes,
            } => {
                // Node 0 leads into the cycle but isn't part of it
                // So it should be in sorted
                assert_eq!(sorted.len(), 1);
                assert!(sorted.contains(&StructId(0)));

                // All nodes in 1->2->3->4->1 are part of the cycle
                assert_eq!(cycle_nodes.len(), 4);
                assert!(cycle_nodes.contains(&StructId(1)));
                assert!(cycle_nodes.contains(&StructId(2)));
                assert!(cycle_nodes.contains(&StructId(3)));
                assert!(cycle_nodes.contains(&StructId(4)));
            }
            _ => panic!("Expected cycle detection"),
        }
    }
}
