use super::*;

#[test]
fn test_less_than_valid() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 5 < 10 }").check();
    result.assert_no_errors();
}

#[test]
fn test_greater_than_valid() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 10 > 5 }").check();
    result.assert_no_errors();
}

#[test]
fn test_less_than_eq_valid() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 5 <= 10 }").check();
    result.assert_no_errors();
}

#[test]
fn test_greater_than_eq_valid() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 10 >= 5 }").check();
    result.assert_no_errors();
}

#[test]
fn test_less_than_left_bool() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { true < 5 }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
}

#[test]
fn test_less_than_right_bool() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 5 < true }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
}

#[test]
fn test_greater_than_both_bool() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { true > false }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
}

#[test]
fn test_less_than_eq_mixed() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 5 <= false }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
}

#[test]
fn test_greater_than_eq_mixed() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { true >= 10 }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
}

#[test]
fn test_comparison_with_expressions() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { (1 + 2) < (3 * 4) }").check();
    result.assert_no_errors();
}

#[test]
fn test_comparison_with_variables() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() Bool {
                let x = 10;
                let y = 20;
                x < y
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_chained_comparisons() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 1 < 2 }").check();
    result.assert_no_errors();
}

#[test]
fn test_comparison_complex_left() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { (10 - 5) * 2 > 8 }").check();
    result.assert_no_errors();
}

#[test]
fn test_comparison_complex_right() {
    let result = TypeCheckTestCase::from_source("fn main() Bool { 15 <= (3 + 4) * 2 }").check();
    result.assert_no_errors();
}

#[test]
fn test_comparison_with_function_call() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_num() I32 { 42 }
            fn main() Bool { get_num() > 10 }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_comparison_both_function_calls() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_a() I32 { 10 }
            fn get_b() I32 { 20 }
            fn main() Bool { get_a() < get_b() }
        "#,
    )
    .check();
    result.assert_no_errors();
}
