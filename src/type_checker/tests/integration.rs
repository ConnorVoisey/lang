use super::*;

#[test]
fn test_multiple_errors_in_function() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn foo() I32 {
                let x = true + false;
                let y = 10 < "hello";
                if 5 { 1 } else { 2 }
            }
            fn main() I32 { 0 }
        "#,
    )
    .check();
    assert!(result.len() >= 3);
}

#[test]
fn test_complex_nested_expression() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                ((1 + 2) * (3 - 4)) / ((5 + 6) - (7 * 8))
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_calling_function() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn helper(x I32) I32 { x * 2 }
            fn caller(y I32) I32 { helper(y + 1) }
            fn main() I32 { caller(10) }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_mixed_control_flow() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let result = 0;
                while result < 10 {
                    if result < 5 {
                        result = result + 1;
                    } else {
                        break;
                    };
                };
                result
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_deep_nesting() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                if true {
                    let x = {
                        if false {
                            while false {
                                break;
                            };
                            10
                        } else {
                            20
                        }
                    };
                    x + 5
                } else {
                    0
                }
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_program_with_multiple_functions() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn add(a I32, b I32) I32 { a + b }
            fn sub(a I32, b I32) I32 { a - b }
            fn mul(a I32, b I32) I32 { a * b }
            fn div(a I32, b I32) I32 { a / b }
            fn main() I32 {
                add(10, sub(20, mul(3, div(12, 4))))
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_with_struct_param() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn use_point(p Point) I32 { p.x + p.y }
            fn main() I32 {
                let pt = Point { x: 5, y: 10 };
                use_point(pt)
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_function_returning_struct() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn make_point(x I32, y I32) Point {
                Point { x: x, y: y }
            }
            fn main() I32 {
                let p = make_point(10, 20);
                p.x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_deeply_nested_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_complex_boolean_expression() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() Bool {
                (1 < 2) == (4 > 3)
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_boolean_expression() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() Bool {
                true == false
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}
