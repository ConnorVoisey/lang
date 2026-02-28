use super::*;

#[test]
fn test_struct_field_access() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                p.x
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_struct_creation_all_fields() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_struct_creation_missing_field() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10 };
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_struct_creation_extra_field() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20, z: 30 };
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_struct_creation_wrong_field_type() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: true, y: 20 };
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_struct_creation_duplicate_field() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, x: 20 };
                0
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}

#[test]
fn test_empty_struct() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Empty { }
            fn main() I32 {
                let e = Empty { };
                0
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_struct_as_function_param() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn use_point(p Point) I32 { 0 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                use_point(p)
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_struct_field_in_arithmetic() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                p.x + p.y
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_nested_struct_field_access() {
    let result = TypeCheckTestCase::from_source(
        r#"
            struct Inner { val I32 }
            struct Outer { inner Inner }
            fn main() I32 {
                let inner = Inner { val: 42 };
                let outer = Outer { inner: inner };
                outer.inner.val
            }
        "#,
    )
    .check();
    result.assert_no_errors();
}

#[test]
fn test_field_access_on_non_struct() {
    let result = TypeCheckTestCase::from_source(
        r#"
            fn main() I32 {
                let x = 42;
                x.field
            }
        "#,
    )
    .check();
    result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
}
