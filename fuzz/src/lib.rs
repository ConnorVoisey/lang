use arbitrary::{Arbitrary, Unstructured};
use lang::interner::{IdentId, Interner, SharedInterner};
use lang::lexer::{Span, Token, TokenKind};
use parking_lot::RwLock;
use std::sync::Arc;

const IDENT_STRINGS: &[&str] = &[
    // Built-in type names (resolved by parser in parse_var_type)
    "U8", "U32", "U64", "I32", "Str", "CStr", "CChar", "Bool",
    // Common identifiers
    "foo", "bar", "baz", "main", "test", "x", "y", "n", "i",
    // Struct/enum names
    "MyStruct", "Point", "Color",
    // Field/method names
    "field", "value", "len",
    // Extern
    "printf", "C",
];

pub fn setup_interner() -> SharedInterner {
    let mut interner = Interner::new();
    for s in IDENT_STRINGS {
        interner.lookup_ident(s);
    }
    Arc::new(RwLock::new(interner))
}

pub struct FuzzToken(pub Token);

impl<'a> Arbitrary<'a> for FuzzToken {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let kind = fuzz_token_kind(u)?;
        Ok(FuzzToken(Token {
            span: Span { start: 0, end: 0 },
            kind,
        }))
    }
}

fn fuzz_token_kind(u: &mut Unstructured) -> arbitrary::Result<TokenKind> {
    let variant: u8 = u.int_in_range(0..=33)?;
    Ok(match variant {
        0 => {
            let idx: usize = u.int_in_range(0..=IDENT_STRINGS.len() - 1)?;
            TokenKind::Ident(IdentId(idx))
        }
        1 => TokenKind::CStr(String::arbitrary(u)?),
        2 => TokenKind::Str(String::arbitrary(u)?),
        3 => TokenKind::Int(i128::arbitrary(u)?),
        4 => TokenKind::SemiColon,
        5 => TokenKind::Colon,
        6 => TokenKind::DoubleColon,
        7 => TokenKind::BracketOpen,
        8 => TokenKind::BracketClose,
        9 => TokenKind::SquareBracketOpen,
        10 => TokenKind::SquareBracketClose,
        11 => TokenKind::CurlyBracketOpen,
        12 => TokenKind::CurlyBracketClose,
        13 => TokenKind::GreaterThan,
        14 => TokenKind::GreaterThanEq,
        15 => TokenKind::LessThan,
        16 => TokenKind::LessThanEq,
        17 => TokenKind::Astrix,
        18 => TokenKind::Slash,
        19 => TokenKind::Add,
        20 => TokenKind::Subtract,
        21 => TokenKind::Assign,
        22 => TokenKind::Equivalent,
        23 => TokenKind::NotEquivalent,
        24 => TokenKind::BinInverse,
        25 => TokenKind::Comma,
        26 => TokenKind::Dot,
        27 => TokenKind::Amp,
        28 => TokenKind::LetKeyWord,
        29 => TokenKind::FnKeyWord,
        30 => TokenKind::ImportKeyWord,
        31 => TokenKind::ExternKeyWord,
        32 => TokenKind::StructKeyWord,
        33 => match u.int_in_range(0..=7)? {
            0 => TokenKind::EnumKeyWord,
            1 => TokenKind::MatchKeyWord,
            2 => TokenKind::ReturnKeyWord,
            3 => TokenKind::IfKeyWord,
            4 => TokenKind::ElseKeyWord,
            5 => TokenKind::TrueKeyWord,
            6 => TokenKind::FalseKeyWord,
            7 => TokenKind::WhileKeyWord,
            _ => TokenKind::BreakKeyWord,
        },
        _ => unreachable!(),
    })
}
