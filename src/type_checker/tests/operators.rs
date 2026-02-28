use super::*;

// ===== Negation Operator =====

#[test]
fn test_negation_on_int() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { -42 }").check();
    result.assert_no_errors();
}

#[test]
fn test_negation_on_bool() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { -true }").check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_negation_on_string() {
    let result = TypeCheckTestCase::from_source(r#"fn main() I32 { -"hello" }"#).check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_double_negation() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { --5 }").check();
    result.assert_no_errors();
}

#[test]
fn test_triple_negation() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { ---10 }").check();
    result.assert_no_errors();
}

#[test]
fn test_negation_on_expression() {
    let result = TypeCheckTestCase::from_source("fn main() I32 { -(5 + 3) }").check();
    result.assert_no_errors();
}

// ===== Reference Operator =====

#[test]
fn test_reference_on_int() {
    let result = TypeCheckTestCase::from_source("fn main() &I32 { &42 }").check();
    result.assert_no_errors();
}

#[test]
fn test_reference_on_bool() {
    let result = TypeCheckTestCase::from_source("fn main() &Bool { &true }").check();
    result.assert_no_errors();
}

#[test]
fn test_nested_reference() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 5;
                let y = &x;
                10
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_reference_in_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 5;
                let y = &x;
                10
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}
