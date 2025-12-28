use crate::{
    ast::{Ast, VarType, error::AstParseError},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{EnumSymbolData, SymbolId, SymbolKind, SymbolTable},
    types::{EnumId, TypeId},
};

#[derive(Debug)]
pub struct AstEnum {
    pub ident_token_at: usize,
    pub ident_id: IdentId,
    pub symbol_id: SymbolId,
    pub enum_id: EnumId,
    pub type_id: Option<TypeId>,
    pub variants: Vec<(IdentId, usize, VarType)>,
}

impl Ast {
    pub fn parse_enum(&mut self, symbols: &mut SymbolTable) {
        let start_token_i = self.curr_token_i();
        assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::EnumKeyWord,
                    ..
                })
            ),
            "Called parsed enum not on a enumKeyWord"
        );

        // expect ident
        let ident_id = *match self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
                ..
            }) => id,
            Some(token) => {
                let cloned_token = token.clone();
                self.errs.push(AstParseError::EnumExpectedIdent {
                    token: cloned_token,
                });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };
        let ident_token_at = self.curr_token_i();

        if symbols.lookup(ident_id).is_some() {
            self.errs.push(AstParseError::EnumDuplicateStructNames {
                token: self.curr_token().unwrap().clone(),
                name: self.interner.read().resolve(ident_id).to_string(),
            });
        }
        // expect `{`
        match self.next_token() {
            Some(Token {
                kind: TokenKind::CurlyBracketOpen,
                ..
            }) => (),
            Some(token) => {
                let cloned_token = token.clone();
                self.errs.push(AstParseError::EnumExpectedCurlyOpen {
                    token: cloned_token,
                });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };

        let mut variants = vec![];

        while let Some(token) = self.next_token() {
            // TODO: remove this clone, only needed for borrow checking in the bracketOpen case
            let token_kind = token.kind.clone();
            match token_kind {
                TokenKind::Ident(ident_id) => match self.peek_token() {
                    Some(Token {
                        kind: TokenKind::Comma,
                        ..
                    }) => {
                        variants.push((ident_id, self.curr_token_i(), VarType::Void));
                        self.next_token();
                    }
                    Some(Token {
                        kind: TokenKind::BracketOpen,
                        ..
                    }) => {
                        self.next_token();
                        let (var_type, span) = self.parse_var_type();
                        variants.push((ident_id, span.start, var_type));
                        match self.peek_token() {
                            Some(Token {
                                kind: TokenKind::BracketClose,
                                ..
                            }) => {
                                self.next_token();
                                if let Some(Token {
                                    kind: TokenKind::Comma,
                                    ..
                                }) = self.peek_token()
                                {
                                    self.next_token();
                                }
                            }
                            t => {
                                dbg!(t);
                                panic!()
                            }
                        }
                    }
                    Some(Token {
                        kind: TokenKind::CurlyBracketClose,
                        ..
                    }) => {
                        variants.push((ident_id, self.curr_token_i(), VarType::Void));
                        break;
                    }
                    t => {
                        dbg!(t);
                        todo!();
                    }
                },
                TokenKind::CurlyBracketClose => break,
                t => {
                    dbg!(t);
                    todo!();
                }
            }
        }
        let full_def_span = Span {
            start: self.tokens[start_token_i].span.start,
            end: self.tokens[self.curr_token_i()].span.end,
        };
        let ident_span = self.tokens[ident_token_at].span.clone();
        let _field_count = variants.len();
        let enum_id = EnumId(self.enums.len());
        let enum_val = AstEnum {
            ident_id,
            ident_token_at,
            symbol_id: symbols.declare(
                ident_id,
                SymbolKind::Enum(EnumSymbolData {
                    enum_id,
                    full_def_span,
                }),
                ident_span,
            ),
            enum_id,
            type_id: None,
            variants,
        };
        self.enums.push(enum_val);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{Ast, VarType, ast_expr::debug::parse_debug_setup},
        interner::IdentId,
    };
    use pretty_assertions::assert_eq;

    fn debug_enums(ast: &Ast) -> Vec<Vec<(String, VarType)>> {
        let i = ast.interner.read();
        ast.enums
            .iter()
            .map(|e| {
                e.variants
                    .iter()
                    .map(|v| (i.resolve(v.0).to_string(), v.2.clone()))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn basic_enum() {
        let (mut ast, mut symbols) = parse_debug_setup("enum Foo { Bar, Baz, }");
        ast.next_token();
        ast.parse_enum(&mut symbols);
        assert_eq!(
            debug_enums(&ast),
            vec![vec![
                ("Bar".to_string(), VarType::Void),
                ("Baz".to_string(), VarType::Void)
            ]]
        );
    }

    #[test]
    fn enum_with_basic_union() {
        let (mut ast, mut symbols) = parse_debug_setup("enum Foo { Bar(Str), Baz(Int) }");
        ast.next_token();
        ast.parse_enum(&mut symbols);
        dbg!(&ast.enums);
        assert_eq!(
            debug_enums(&ast),
            vec![vec![
                ("Bar".to_string(), VarType::Str),
                ("Baz".to_string(), VarType::Int)
            ]]
        );
    }

    #[test]
    fn enum_with_struct() {
        let (mut ast, mut symbols) = parse_debug_setup(
            r#"
struct Coordinate {
    x Int,
    y Int,
}

enum Foo {
    Bar(Coordinate),
    Baz(&Coordinate),
}
"#,
        );
        ast.next_token();
        ast.parse_struct(&mut symbols);
        ast.next_token();
        ast.parse_enum(&mut symbols);
        dbg!(&ast.enums);
        assert_eq!(
            debug_enums(&ast),
            vec![vec![
                ("Bar".to_string(), VarType::Custom((IdentId(0), None))),
                (
                    "Baz".to_string(),
                    VarType::Ref(Box::new(VarType::Custom((IdentId(0), None))))
                )
            ]]
        );
    }

    #[test]
    fn enum_with_enum() {
        let (mut ast, mut symbols) = parse_debug_setup(
            r#"
enum Foo {
    Var1(Bar),
    Var2,
}
enum Bar {
    Var3(&Foo),
    Var4,
}
"#,
        );
        ast.next_token();
        ast.parse_enum(&mut symbols);
        ast.next_token();
        ast.parse_enum(&mut symbols);
        dbg!(&ast.enums);
        assert_eq!(
            debug_enums(&ast),
            vec![
                vec![
                    ("Var1".to_string(), VarType::Custom((IdentId(2), None))),
                    ("Var2".to_string(), VarType::Void,)
                ],
                vec![
                    (
                        "Var3".to_string(),
                        VarType::Ref(Box::new(VarType::Custom((IdentId(0), None))))
                    ),
                    ("Var4".to_string(), VarType::Void,)
                ]
            ]
        );
    }
}
