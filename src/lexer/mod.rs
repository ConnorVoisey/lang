use crate::{
    interner::{IdentId, Interner, SharedInterner},
    lexer::error::LexerError,
};
use std::{fs::read_to_string, iter::Peekable, str::CharIndices};

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
    DoubleColon,
    BracketOpen,
    BracketClose,
    SquareBracketOpen,
    SquareBracketClose,
    CurlyBracketOpen,
    CurlyBracketClose,
    GreaterThan,
    LessThan,
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
    ReturnKeyWord,
    IfKeyWord,
    ElseKeyWord,
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
    pub fn from_src_str(src: &'src str, interner: &SharedInterner) -> Result<Self, LexerError> {
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
                        lexer.errs.push(LexerError::UnhandledChar {
                            char: ':',
                            span: Span {
                                start: i,
                                end: i + 1,
                            },
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
                '>' => TokenKind::GreaterThan,
                '<' => TokenKind::LessThan,
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
                '"' => {
                    end_i = *i;
                    chars.next();
                    if let Some('\\') = val.chars().last() {
                        continue;
                    }
                    has_ended_str = true;
                    break;
                }
                _ => {
                    val.push(*char);
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
            "return" => TokenKind::ReturnKeyWord,
            "if" => TokenKind::IfKeyWord,
            "else" => TokenKind::ElseKeyWord,
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
    use crate::lexer::{Lexer, TokenKind};
    use pretty_assertions::assert_eq;

    #[test]
    fn basic_lexing() {
        let src = "fn test(ident Int, ident_underscore C_Char, c_char Str)".to_string();
        let tokens = Lexer::from_src_str(src).unwrap().tokens;
        assert_eq!(
            tokens
                .iter()
                .map(|token| token.kind.clone())
                .collect::<Vec<_>>(),
            vec![
                TokenKind::FnKeyWord,
                TokenKind::Ident("test".to_string()),
                TokenKind::BracketOpen,
                TokenKind::Ident("ident".to_string()),
                TokenKind::Ident("Int".to_string()),
                TokenKind::Comma,
                TokenKind::Ident("ident_underscore".to_string()),
                TokenKind::Ident("C_Char".to_string()),
                TokenKind::Comma,
                TokenKind::Ident("c_char".to_string()),
                TokenKind::Ident("Str".to_string()),
                TokenKind::BracketClose,
            ]
        );
    }
}
