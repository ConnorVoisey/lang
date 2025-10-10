use crate::{
    ast::{Ast, VarType, error::AstParseError},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolKind, SymbolTable},
    types::{StructId, TypeId},
};

#[derive(Debug)]
pub struct AstStruct {
    pub ident_token_at: usize,
    pub ident_id: IdentId,
    pub symbol_id: SymbolId,
    pub struct_id: StructId,
    pub type_id: Option<TypeId>,
    pub fields: Vec<(IdentId, usize, VarType)>,
    pub field_type_ids: Vec<Option<TypeId>>,
}

impl Ast {
    pub fn parse_struct(&mut self, symbols: &mut SymbolTable) {
        let start_token_i = self.curr_token_i();
        assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::StructKeyWord,
                    ..
                })
            ),
            "Called parsed struct not on a structKeyWord"
        );

        // expect ident
        let ident_id = *match self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
                ..
            }) => id,
            Some(token) => {
                let cloned_token = token.clone();
                self.errs.push(AstParseError::StructExpectedIdent {
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
            self.errs.push(AstParseError::StructDuplicateStructNames {
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
                self.errs.push(AstParseError::StructExpectedCurlyOpen {
                    token: cloned_token,
                });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };

        let mut fields = vec![];

        while let Some(token) = self.next_token() {
            match &token.kind {
                TokenKind::Ident(field_ident_id) => {
                    let field_ident_id = *field_ident_id;
                    let ident_token_at = self.curr_token_i();
                    let (var_type, _type_span) = self.parse_var_type();
                    fields.push((field_ident_id, ident_token_at, var_type));
                    match self.next_token() {
                        Some(Token {
                            kind: TokenKind::Comma,
                            ..
                        }) => {
                            continue;
                        }
                        Some(Token {
                            kind: TokenKind::CurlyBracketClose,
                            ..
                        }) => {
                            break;
                        }
                        t => {
                            dbg!(t);
                            todo!();
                        }
                    }
                }
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
        let field_count = fields.len();
        let struct_id = StructId(self.structs.len());
        let struct_val = AstStruct {
            ident_id,
            ident_token_at,
            symbol_id: symbols.declare(
                ident_id,
                SymbolKind::Struct(crate::symbols::StructSymbolData {
                    struct_id,
                    full_def_span,
                }),
                ident_span,
            ),
            struct_id,
            type_id: None,
            fields,
            field_type_ids: vec![None; field_count],
        };
        self.structs.push(struct_val);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{Ast, VarType},
        interner::{Interner, SharedInterner},
        lexer::{Lexer, Token, TokenKind},
        symbols::SymbolTable,
    };
    use parking_lot::RwLock;
    use pretty_assertions::assert_eq;

    #[test]
    fn basic_struct() {
        let src = String::from(
            r#"struct CLikeStr {
    len Uint,
    chars &CChar
}"#,
        );
        let interner = Interner::new();
        let shared_interner = SharedInterner::new(RwLock::new(interner));
        let lexer = Lexer::from_src_str(&src, &shared_interner).unwrap();
        let mut ast = Ast::new(lexer.tokens, shared_interner.clone());
        let mut symbols = SymbolTable::new(shared_interner.clone());
        ast.next_token();
        ast.parse_struct(&mut symbols);
        assert_eq!(ast.structs.len(), 1, "expected 1 struct to be found");

        let mut i = shared_interner.write();
        let struct_val = ast.structs.first().unwrap();
        assert_eq!(
            match &ast.tokens[struct_val.ident_token_at].kind {
                TokenKind::Ident(id) => i.resolve(*id).to_string(),
                t => format!("Expected ident got: {t:?}"),
            },
            "CLikeStr".to_string(),
            "expected 1 struct to be found"
        );
        let fields_mapped = struct_val
            .fields
            .iter()
            .map(|f| (i.resolve(f.0).to_string(), f.2.clone()))
            .collect::<Vec<_>>();
        let expected = vec![
            ("len".to_string(), VarType::Uint),
            ("chars".to_string(), VarType::Ref(Box::new(VarType::CChar))),
        ];
        assert_eq!(fields_mapped, expected);
    }
}
