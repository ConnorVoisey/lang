use tracing::info;

use crate::{
    interner::{IdentId, SharedInterner},
    lexer::error::LexerError,
};
use std::{iter::Peekable, str::CharIndices};

pub mod error;

#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Ident(IdentId),
    CStr(String),
    Str(String),
    Int(i32),
    SemiColon,
    Colon,
    DoubleColon,
    BracketOpen,
    BracketClose,
    SquareBracketOpen,
    SquareBracketClose,
    CurlyBracketOpen,
    CurlyBracketClose,
    GreaterThan,
    GreaterThanEq,
    LessThan,
    LessThanEq,
    Astrix,
    Slash,
    Add,
    Subtract,
    Assign,
    Equivalent,
    Comma,
    Dot,
    Amp,
    LetKeyWord,
    FnKeyWord,
    ImportKeyWord,
    ExternKeyWord,
    StructKeyWord,
    EnumKeyWord,
    MatchKeyWord,
    ReturnKeyWord,
    IfKeyWord,
    ElseKeyWord,
    TrueKeyWord,
    FalseKeyWord,
    WhileKeyWord,
    BreakKeyWord,
}
#[derive(Debug, Clone)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}
#[derive(Debug)]
pub struct Lexer<'src> {
    pub src: &'src str,
    pub tokens: Vec<Token>,
    pub errs: Vec<LexerError>,
}
#[derive(Debug)]
pub enum StrType {
    Str,
    CStr,
}

impl<'src> Lexer<'src> {
    #[tracing::instrument(skip(src, interner))]
    pub fn from_src_str(src: &'src str, interner: &SharedInterner) -> Result<Self, LexerError> {
        info!("started lexing");
        let mut chars = src.char_indices().peekable();
        let mut lexer = Lexer {
            src,
            tokens: vec![],
            errs: vec![],
        };
        while let Some((i, char)) = chars.next() {
            let kind = match char {
                t if t.is_whitespace() => continue,
                'c' => {
                    match chars.peek() {
                        Some((_, '"')) => {
                            chars.next();
                            lexer.parse_string(i, &mut chars, StrType::CStr)
                        }
                        _ => lexer.parse_ident(i, &mut chars, interner),
                    }
                    continue;
                }
                ';' => TokenKind::SemiColon,
                ':' => match chars.peek() {
                    Some(&(_, ':')) => {
                        chars.next();
                        lexer.tokens.push(Token {
                            span: Span {
                                start: i,
                                end: i + 1,
                            },
                            kind: TokenKind::DoubleColon,
                        });
                        continue;
                    }
                    _ => {
                        lexer.tokens.push(Token {
                            span: Span {
                                start: i,
                                end: i + 1,
                            },
                            kind: TokenKind::Colon,
                        });
                        continue;
                    }
                },
                '[' => TokenKind::SquareBracketOpen,
                ']' => TokenKind::SquareBracketClose,
                '(' => TokenKind::BracketOpen,
                ')' => TokenKind::BracketClose,
                '{' => TokenKind::CurlyBracketOpen,
                '}' => TokenKind::CurlyBracketClose,
                '*' => TokenKind::Astrix,
                '/' => match chars.peek() {
                    Some(&(_, '/')) => {
                        loop {
                            match chars.next() {
                                Some((_, '\n')) => break,
                                Some(_) => continue,
                                None => break,
                            }
                        }
                        continue;
                    }
                    _ => TokenKind::Slash,
                },
                '>' => match chars.peek() {
                    Some(&(_, '=')) => {
                        chars.next();
                        TokenKind::GreaterThanEq
                    }
                    _ => TokenKind::GreaterThan,
                },
                '<' => match chars.peek() {
                    Some(&(_, '=')) => {
                        chars.next();
                        TokenKind::LessThanEq
                    }
                    _ => TokenKind::LessThan,
                },
                '+' => TokenKind::Add,
                '-' => TokenKind::Subtract,
                '=' => match chars.peek() {
                    Some(&(_, '=')) => {
                        chars.next();
                        lexer.tokens.push(Token {
                            span: Span {
                                start: i,
                                end: i + 1,
                            },
                            kind: TokenKind::Equivalent,
                        });
                        continue;
                    }
                    _ => TokenKind::Assign,
                },
                ',' => TokenKind::Comma,
                '.' => TokenKind::Dot,
                '&' => TokenKind::Amp,
                '"' => {
                    lexer.parse_string(i, &mut chars, StrType::Str);
                    continue;
                }
                t if t.is_ascii_digit() => {
                    lexer.parse_num(t, i, &mut chars);
                    continue;
                }
                t if t.is_alphabetic() => {
                    lexer.parse_ident(i, &mut chars, interner);
                    continue;
                }
                t => {
                    lexer.errs.push(LexerError::UnhandledChar {
                        char: t,
                        span: Span {
                            start: i,
                            end: i + 1,
                        },
                    });
                    continue;
                }
            };
            lexer.tokens.push(Token {
                span: Span {
                    start: i,
                    end: i + 1,
                },
                kind,
            })
        }
        info!("finished lexing");
        Ok(lexer)
    }

    fn parse_string(
        &mut self,
        start_i: usize,
        chars: &mut Peekable<CharIndices>,
        str_type: StrType,
    ) {
        let mut val = String::new();

        let mut end_i = start_i;
        let mut has_ended_str = false;
        while let Some((i, char)) = chars.peek() {
            match *char {
                '\\' => {
                    chars.next();
                    match chars.peek() {
                        Some((i, 'n')) => {
                            end_i = *i;
                            val.push('\n');
                            chars.next();
                        }
                        Some((i, 'r')) => {
                            end_i = *i;
                            val.push('\r');
                            chars.next();
                        }
                        Some((i, 't')) => {
                            end_i = *i;
                            val.push('\t');
                            chars.next();
                        }
                        Some((i, '0')) => {
                            end_i = *i;
                            val.push('\0');
                            chars.next();
                        }
                        Some((i, '"')) => {
                            end_i = *i;
                            val.push('\"');
                            chars.next();
                        }
                        Some((i, '\'')) => {
                            end_i = *i;
                            val.push('\'');
                            chars.next();
                        }
                        Some((i, char_val)) => {
                            self.errs.push(LexerError::UnhandledSlashChar {
                                span: Span {
                                    start: *i - 1,
                                    end: *i + 1,
                                },
                                char: *char_val,
                            });
                            chars.next();
                        }
                        None => {
                            val.push('\\');
                            chars.next();
                            end_i += 1;
                        }
                    }
                }
                '"' => {
                    end_i = *i;
                    chars.next();
                    has_ended_str = true;
                    break;
                }
                _ => {
                    val.push(*char);
                    end_i = *i;
                    chars.next();
                }
            }
        }
        if !has_ended_str {
            self.errs.push(LexerError::UnclosedString {
                span: Span {
                    start: start_i,
                    end: start_i,
                },
            });
            return;
        }
        let kind = match str_type {
            StrType::Str => TokenKind::Str(val),
            StrType::CStr => TokenKind::CStr(val),
        };
        self.tokens.push(Token {
            span: Span {
                start: start_i,
                end: end_i,
            },
            kind,
        });
    }
    fn parse_ident(
        &mut self,
        start_i: usize,
        chars: &mut Peekable<CharIndices>,
        interner: &SharedInterner,
    ) {
        let mut end_i = start_i;
        while let Some((i, char)) = chars.peek() {
            if !char.is_alphanumeric() && *char != '_' {
                end_i = *i;
                break;
            }
            chars.next();
        }

        let val = &self.src[start_i..end_i];
        let kind = match val {
            "let" => TokenKind::LetKeyWord,
            "fn" => TokenKind::FnKeyWord,
            "import" => TokenKind::ImportKeyWord,
            "extern" => TokenKind::ExternKeyWord,
            "struct" => TokenKind::StructKeyWord,
            "enum" => TokenKind::EnumKeyWord,
            "match" => TokenKind::MatchKeyWord,
            "return" => TokenKind::ReturnKeyWord,
            "if" => TokenKind::IfKeyWord,
            "else" => TokenKind::ElseKeyWord,
            "true" => TokenKind::TrueKeyWord,
            "false" => TokenKind::FalseKeyWord,
            "while" => TokenKind::WhileKeyWord,
            "break" => TokenKind::BreakKeyWord,
            _ => {
                let mut interner_writable = interner.write();
                let id = interner_writable.lookup_ident(val);
                TokenKind::Ident(id)
            }
        };
        self.tokens.push(Token {
            span: Span {
                start: start_i,
                end: end_i,
            },
            kind,
        });
    }
    fn parse_num(&mut self, first: char, start_i: usize, chars: &mut Peekable<CharIndices>) {
        let mut num_str = first.to_string();

        let mut end_i = start_i;
        while let Some((i, char)) = chars.peek() {
            if *char == '_' {
                chars.next();
                continue;
            }
            if !char.is_ascii_digit() {
                end_i = *i;
                break;
            }

            num_str.push(*char);
            chars.next();
        }
        let val = match num_str.parse() {
            Ok(v) => v,
            Err(e) => {
                self.errs.push(LexerError::ParseDigitStrToInt(e));
                return;
            }
        };

        self.tokens.push(Token {
            span: Span {
                start: start_i,
                end: end_i,
            },
            kind: TokenKind::Int(val),
        });
    }
}

impl TokenKind {
    pub fn is_op(&self) -> bool {
        !matches!(
            self,
            TokenKind::Ident(_) | TokenKind::CStr(_) | TokenKind::Str(_) | TokenKind::Int(_)
        )
    }
}
#[cfg(test)]
mod test {
    use crate::{
        interner::{Interner, SharedInterner},
        lexer::{Lexer, TokenKind},
    };
    use parking_lot::RwLock;
    use pretty_assertions::assert_eq;

    #[test]
    fn basic_lexing() {
        let src =
            "fn test(ident Int, ident_underscore C_Char, c_char Str) Int {let foo = c\"test\\n\"}"
                .to_string();
        let interner = Interner::new();
        let shared_interner = SharedInterner::new(RwLock::new(interner));
        let tokens = Lexer::from_src_str(&src, &shared_interner).unwrap().tokens;
        let mut i = shared_interner.write();
        assert_eq!(
            tokens
                .iter()
                .map(|token| token.kind.clone())
                .collect::<Vec<_>>(),
            vec![
                TokenKind::FnKeyWord,
                TokenKind::Ident(i.lookup_ident("test")),
                TokenKind::BracketOpen,
                TokenKind::Ident(i.lookup_ident("ident")),
                TokenKind::Ident(i.lookup_ident("Int")),
                TokenKind::Comma,
                TokenKind::Ident(i.lookup_ident("ident_underscore")),
                TokenKind::Ident(i.lookup_ident("C_Char")),
                TokenKind::Comma,
                TokenKind::Ident(i.lookup_ident("c_char")),
                TokenKind::Ident(i.lookup_ident("Str")),
                TokenKind::BracketClose,
                TokenKind::Ident(i.lookup_ident("Int")),
                TokenKind::CurlyBracketOpen,
                TokenKind::LetKeyWord,
                TokenKind::Ident(i.lookup_ident("foo")),
                TokenKind::Assign,
                TokenKind::CStr(String::from("test\n")),
                TokenKind::CurlyBracketClose,
            ]
        );
    }
}
