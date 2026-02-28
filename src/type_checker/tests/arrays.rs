use super::*;

#[test]
fn test_array_init_homogeneous_ints() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [1, 2, 3];
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_array_init_homogeneous_bools() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [true, false, true];
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_array_init_heterogeneous() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [1, true, 3];
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_array_init_empty() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [];
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ArrayNoInnerType { .. }));
}

#[test]
fn test_array_with_expressions() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [1 + 2, 3 * 4, 5 - 1];
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_array_with_function_results() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let arr = [get_val(), get_val()];
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_nested_arrays() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [[1, 2], [3, 4]];
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_array_mixed_expr_types() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let arr = [10, true];
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}
