use super::*;

#[test]
fn test_explicit_return_matching() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                return 42;
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_explicit_return_mismatched() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                return true;
            }
            fn main() I32 { 0 }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
}

#[test]
fn test_block_return_matching() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 42 }").check();
    result.assert_no_errors();
}

#[test]
fn test_block_return_mismatched() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { true }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
}

#[test]
fn test_return_in_nested_block() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                {
                    return 42;
                }
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_return_in_if_branch() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                if true {
                    return 42;
                } else {
                    return 0;
                }
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_return_in_else_branch() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                if false {
                    0
                } else {
                    return 42;
                }
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_early_return_wrong_type() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                if true {
                    return false;
                };
                42
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
}

#[test]
fn test_multiple_returns_all_matching() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo(x I32) I32 {
                if x < 0 {
                    return 0;
                };
                if x > 100 {
                    return 100;
                };
                x
            }
            fn main() I32 { foo(50) }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_return_with_expression() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                return 10 + 20 * 3;
            }
            fn main() I32 { foo() }
        "#,
    )
    .check();
    result.assert_no_errors();
}
