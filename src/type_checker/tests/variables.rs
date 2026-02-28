use super::*;

// ===== Variable Declarations =====

#[test]
fn test_var_decl_int() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 42;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_var_decl_bool() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() Bool {
                let x = true;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_var_decl_with_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10 + 20;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_var_decl_with_function_call() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let x = get_val();
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_multiple_var_decls() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                let z = 30;
                x + y + z
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_var_decl_complex_expr() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = (10 + 20) * 3 - 5;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

// ===== Assignments =====

#[test]
fn test_assignment_compatible_type() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                x = 20;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_assignment_incompatible_int_to_bool() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = true;
                x = 10;
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::AssignmentMismatch { .. }));
}

#[test]
fn test_assignment_incompatible_bool_to_int() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                x = true;
                x
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::AssignmentMismatch { .. }));
}

#[test]
fn test_assignment_function_result() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let x = 0;
                x = get_val();
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_assignment_arithmetic_result() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                x = x + 5;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_multiple_assignments() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                x = 30;
                y = 40;
                x + y
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_reassignment_same_type() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 10;
                x = 20;
                x = 30;
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_assignment_to_if_result() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 0;
                x = if true { 10 } else { 20 };
                x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}
