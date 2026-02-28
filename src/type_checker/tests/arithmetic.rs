use super::*;

#[test]
fn test_simple_addition() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 1 + 2 }").check();
    result.assert_no_errors();
}
#[test]
fn test_mixed_type_arithmetic() {
    let result = TypeCheckTestCase::from_source(r#"fn main() I32 { 1 + true }"#).check();
    result.assert_error_count(1);
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_subtraction_valid() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 10 - 5 }").check();
    result.assert_no_errors();
}

#[test]
fn test_multiplication_valid() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 3 * 7 }").check();
    dbg!(&result);
    result.assert_no_errors();
}

#[test]
fn test_division_valid() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 20 / 4 }").check();
    result.assert_no_errors();
}

#[test]
fn test_subtraction_left_bool() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { true - 5 }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_multiplication_right_bool() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 5 * false }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_division_left_string() {
    let result = TypeCheckTestCase::from_source(r#"fn main() I32 { "hello" / 2 }"#).check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_nested_arithmetic() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { (1 + 2) * (3 - 4) / 5 }").check();
    result.assert_no_errors();
}

#[test]
fn test_arithmetic_with_variables() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                x + y * 2
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_arithmetic_with_function_result() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_num() I32 { 42 }
            fn main() I32 { get_num() + 10 }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_subtraction_both_sides_wrong() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { true - false }").check();
    result.assert_error_count(2);
}

#[test]
fn test_complex_arithmetic_chain() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { 1 + 2 - 3 * 4 / 5 + 6 }").check();
    result.assert_no_errors();
}
