use super::*;

// ===== If Expression Tests =====

#[test]
fn test_if_non_bool_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
              fn main() I32 {
                  if 5 { 1 } else { 2 }
              }
          "#,
    )
    .check();

    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
}

#[test]
fn test_if_else_branch_mismatch() {
    let result = TypeCheckTestCase::from_source(
        r#"
              fn main() I32 {
                  if true { 1 } else { false }
              }
          "#,
    )
    .check();

    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
}

#[test]
fn test_if_bool_literal() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true { 42 } else { 0 }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_comparison_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if 5 < 10 { 1 } else { 2 }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_without_else() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true { 42 };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_else_matching_types() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true { 10 } else { 20 }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_multiple_else_if_matching() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if false { 1 } else if true { 2 } else if false { 3 } else { 4 }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_multiple_else_if_mismatched() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if false { 1 } else if true { false } else { 3 }
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
}

#[test]
fn test_nested_if_expressions() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true {
                    if false { 1 } else { 2 }
                } else {
                    3
                }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_in_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                (if true { 10 } else { 20 }) + 5
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_as_function_arg() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn use_val(x I32) I32 { x }
            fn main() I32 {
                use_val(if true { 5 } else { 10 })
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_else_if_non_bool_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true {
                    1
                } else if 5 {
                    2
                } else {
                    3
                }
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
}

#[test]
fn test_if_with_block_body() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true {
                    let x = 5;
                    x + 10
                } else {
                    20
                }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_else_type_mismatch_bool_int() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true { true } else { 10 }
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
}

#[test]
fn test_if_only_else_if_no_final_else() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if false { 1 } else if true { 2 };
                42
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_if_string_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if "hello" { 1 } else { 2 }
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
}

// ===== While Loops =====

#[test]
fn test_while_bool_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                while true { break; };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_while_int_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                while 5 { break; };
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::WhileConditionNotBool { .. }));
}

#[test]
fn test_while_comparison_condition() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 0;
                while x < 10 { break; };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_while_with_body() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 0;
                while x < 10 {
                    let y = x + 1;
                    break;
                };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_break_inside_while() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                while true { break; };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_break_outside_while() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                break;
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::BreakOutsideLoop { .. }));
}

#[test]
fn test_break_inside_nested_while() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                while true {
                    while false {
                        break;
                    };
                    break;
                };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_while_empty_body() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                while false { };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

// ===== Block Expressions =====

#[test]
fn test_empty_block() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                { };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_block_single_statement() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                { let x = 5; };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_block_multiple_statements() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                {
                    let x = 5;
                    let y = 10;
                    let z = x + y;
                };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_block_with_return_value() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = { 42 };
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_nested_blocks() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                {
                    {
                        {
                            42
                        }
                    }
                }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_block_in_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                { 10 } + { 20 }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}
