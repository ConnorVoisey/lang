use crate::{
    ast::{Ast, error::AstParseError},
    lexer::{Token, TokenKind},
};

impl Ast {
    pub fn parse_imports(&mut self) {
        assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::ImportKeyWord,
                    ..
                })
            ),
            "Called parsed imports not on an import key word"
        );

        // expect `{`
        match self.next_token() {
            Some(Token {
                kind: TokenKind::CurlyBracketOpen,
                ..
            }) => (),
            Some(token) => {
                let cloned_token = token.clone();
                self.errs
                    .push(AstParseError::ImportExpectedCurlyBracketOpen {
                        token: cloned_token,
                    });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };

        // started parsing the imports, expect `}` or string
        while let Some(token) = self.next_token() {
            let cloned_token = token.clone();
            match &token.kind {
                TokenKind::Str(str_val) => {
                    let cloned_str_val = str_val.clone();
                    let existing_imp = self.imports.iter().find(|imp| **imp == cloned_str_val);
                    if existing_imp.is_some() {
                        let cloned_cloned_str_val = cloned_str_val.clone();
                        self.errs.push(AstParseError::ImportDeclaredMultipleTimes {
                            token: cloned_token,
                            str_val: cloned_cloned_str_val,
                        });
                    }
                    self.imports.push(cloned_str_val);
                }
                TokenKind::CurlyBracketClose => break,
                _ => {
                    let cloned_token = token.clone();
                    self.errs.push(AstParseError::ImportExpectedStrOrClose {
                        token: cloned_token,
                    });
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{Ast, VarType},
        lexer::{Lexer, Token, TokenKind},
    };
    use pretty_assertions::assert_eq;

    #[test]
    fn basic_fn_params() {
        let src = String::from(
            "(num_1 Int, num_2 Int, str_val Str, ref_str &Str, ref_ref_str &&Str, custom Custom, c_char CChar)",
        );
        let lexer = Lexer::from_src_str(src).unwrap();
        let mut ast = Ast::new(lexer.tokens);
        ast.next_token();
        let args = ast.parse_fn_args();
        let args_mapped = args
            .iter()
            .map(|arg| {
                (
                    match &ast.tokens[arg.key_token_at] {
                        Token {
                            kind: TokenKind::Ident(ident_val),
                            ..
                        } => ident_val.clone(),
                        t => format!("Expected ident, got: {t:?}"),
                    },
                    arg.var_type.clone(),
                )
            })
            .collect::<Vec<_>>();
        let expected = vec![
            ("num_1".to_string(), VarType::Int),
            ("num_2".to_string(), VarType::Int),
            ("str_val".to_string(), VarType::Str),
            ("ref_str".to_string(), VarType::Ref(Box::new(VarType::Str))),
            (
                "ref_ref_str".to_string(),
                VarType::Ref(Box::new(VarType::Ref(Box::new(VarType::Str)))),
            ),
            ("custom".to_string(), VarType::Custom(20)),
            ("c_char".to_string(), VarType::CChar),
        ];
        assert_eq!(args_mapped, expected);
    }
}
