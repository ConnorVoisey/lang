use super::*;

#[test]
fn test_function_wrong_arg_count() {
    let result = TypeCheckTestCase::from_source(
        r#"
              fn add(a I32, b I32) I32 { a + b }
              fn main() I32 { add(1) }
          "#,
    )
    .check();

    result.assert_error_count(1);
    result.assert_has_error(|e| {
        matches!(
            e,
            TypeCheckingError::MissingFnArgCall {
                expected_arg_count: 2,
                got_arg_count: 1,
                ..
            }
        )
    });
}

#[test]
fn test_function_no_args() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_value() I32 { 42 }
            fn main() I32 { get_value() }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_three_args() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add_three(a I32, b I32, c I32) I32 { a + b + c }
            fn main() I32 { add_three(1, 2, 3) }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_too_many_args() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(1, 2, 3) }
        "#,
    )
    .check();
    result.assert_has_error(|e| {
        matches!(
            e,
            TypeCheckingError::MissingFnArgCall {
                expected_arg_count: 2,
                got_arg_count: 3,
                ..
            }
        )
    });
}

#[test]
fn test_function_wrong_first_arg() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(true, 2) }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
}

#[test]
fn test_function_wrong_second_arg() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(1, false) }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
}

#[test]
fn test_function_wrong_middle_arg() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add_three(a I32, b I32, c I32) I32 { a + b + c }
            fn main() I32 { add_three(1, true, 3) }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
}

#[test]
fn test_function_multiple_wrong_args() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(true, false) }
        "#,
    )
    .check();
    result.assert_error_count(2);
}

#[test]
fn test_nested_function_calls() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn inner(x I32) I32 { x * 2 }
            fn outer(y I32) I32 { inner(y + 1) }
            fn main() I32 { outer(5) }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_call_result_in_expr() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn get_val() I32 { 10 }
            fn main() I32 { get_val() + 5 }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_call_variable_not_function() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 5;
                x()
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::CallNonFunction { .. }));
}

#[test]
fn test_multiple_function_calls_in_expr() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn a() I32 { 1 }
            fn b() I32 { 2 }
            fn c() I32 { 3 }
            fn main() I32 { a() + b() * c() }
        "#,
    )
    .check();
    result.assert_no_errors();
}
