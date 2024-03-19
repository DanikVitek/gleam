use crate::ast::SrcSpan;
use crate::parse::error::{
    InvalidUnicodeEscapeError, LexicalError, LexicalErrorType, ParseError, ParseErrorType,
};
use camino::Utf8PathBuf;

use pretty_assertions::assert_eq;
use proptest::proptest;

macro_rules! assert_error {
    ($src:expr, $error:expr $(,)?) => {
        let result = crate::parse::parse_statement_sequence($src).expect_err("should not parse");
        assert_eq!(($src, $error), ($src, result),);
    };
    ($src:expr) => {
        let result = $crate::parse::tests::expect_error($src);
        insta::assert_snapshot!(insta::internals::AutoName, result, $src);
    };
}

macro_rules! assert_module_error {
    ($src:expr) => {
        let result = $crate::parse::tests::expect_module_error($src);
        insta::assert_snapshot!(insta::internals::AutoName, result, $src);
    };
}

macro_rules! assert_parse_module {
    ($src:expr) => {
        let result = crate::parse::parse_module($src).expect("should parse");
        insta::assert_snapshot!(insta::internals::AutoName, &format!("{:#?}", result), $src);
    };
}

macro_rules! assert_parse {
    ($src:expr) => {
        let result = crate::parse::parse_statement_sequence($src).expect("should parse");
        insta::assert_snapshot!(insta::internals::AutoName, &format!("{:#?}", result), $src);
    };
}

pub fn expect_module_error(src: &str) -> String {
    let result = crate::parse::parse_module(src).expect_err("should not parse");
    let error = crate::error::Error::Parse {
        src: src.into(),
        path: Utf8PathBuf::from("/src/parse/error.gleam"),
        error: result,
    };
    error.pretty_string()
}

pub fn expect_error(src: &str) -> String {
    let result = crate::parse::parse_statement_sequence(src).expect_err("should not parse");
    let error = crate::error::Error::Parse {
        src: src.into(),
        path: Utf8PathBuf::from("/src/parse/error.gleam"),
        error: result,
    };
    error.pretty_string()
}

proptest! {
    #[test]
    fn parse_bad_binary_int(s in r#"0b[01]*[2-9a-fA-F]+"#) {
        let len = s.len() as u32;
        let location = SrcSpan { start: len - 1, end: len - 1 };
        assert_error!(
            &s,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::DigitOutOfRadix,
                        location,
                    }
                },
                location,
            }
        );
    }

    #[test]
    fn parse_bad_octal_int(s in r#"0o[0-7]*[8-9a-fA-F]+"#) {
        let len = s.len() as u32;
        let location = SrcSpan { start: len - 1, end: len - 1 };
        assert_error!(
            &s,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::DigitOutOfRadix,
                        location,
                    }
                },
                location,
            }
        );
    }

    #[test]
    fn parse_bad_radix_int(s in r#"0[xob][^0-9a-fA-F]*"#) {
        let location = SrcSpan { start: 1, end: 1 };
        assert_error!(
            &s,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::RadixIntNoValue,
                        location,
                    }
                },
                location,
            }
        );
    }

    #[test]
    fn parse_bad_int_trailing_underscore(s in r#"([0-9]_?)*[0-9]_"#) {
        let len = s.len() as u32;
        let location = SrcSpan { start: len - 1, end: len - 1 };
        assert_error!(
            &s,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::NumTrailingUnderscore,
                        location,
                    }
                },
                location,
            }
        );
    }
}

#[test]
fn string_bad_character_escape() {
    assert_error!(
        r#""\g""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::BadStringEscape,
                    location: SrcSpan { start: 1, end: 2 },
                }
            },
            location: SrcSpan { start: 1, end: 2 },
        }
    );
}

#[test]
fn string_bad_character_escape_leading_backslash() {
    assert_error!(
        r#""\\\g""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::BadStringEscape,
                    location: SrcSpan { start: 3, end: 4 },
                }
            },
            location: SrcSpan { start: 3, end: 4 },
        }
    );
}

#[test]
fn string_freestanding_unicode_escape_sequence() {
    assert_error!(
        r#""\u""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::MissingOpeningBrace,
                    ),
                    location: SrcSpan { start: 2, end: 3 },
                }
            },
            location: SrcSpan { start: 2, end: 3 },
        }
    );
}

#[test]
fn string_unicode_escape_sequence_no_braces() {
    assert_error!(
        r#""\u65""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::MissingOpeningBrace,
                    ),
                    location: SrcSpan { start: 2, end: 3 },
                }
            },
            location: SrcSpan { start: 2, end: 3 },
        }
    );
}

#[test]
fn string_unicode_escape_sequence_invalid_hex() {
    assert_error!(
        r#""\u{z}""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::ExpectedHexDigitOrCloseBrace,
                    ),
                    location: SrcSpan { start: 4, end: 5 },
                }
            },
            location: SrcSpan { start: 4, end: 5 },
        }
    );
}

#[test]
fn string_unclosed_unicode_escape_sequence() {
    assert_error!(
        r#""\u{039a""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::ExpectedHexDigitOrCloseBrace,
                    ),
                    location: SrcSpan { start: 8, end: 9 },
                }
            },
            location: SrcSpan { start: 8, end: 9 },
        }
    );
}

#[test]
fn string_empty_unicode_escape_sequence() {
    assert_error!(
        r#""\u{}""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::InvalidNumberOfHexDigits,
                    ),
                    location: SrcSpan { start: 1, end: 5 },
                }
            },
            location: SrcSpan { start: 1, end: 5 },
        }
    );
}

#[test]
fn string_overlong_unicode_escape_sequence() {
    assert_error!(
        r#""\u{0011f601}""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::InvalidNumberOfHexDigits,
                    ),
                    location: SrcSpan { start: 1, end: 13 },
                }
            },
            location: SrcSpan { start: 1, end: 13 },
        }
    );
}

#[test]
fn string_invalid_unicode_escape_sequence() {
    assert_error!(
        r#""\u{110000}""#,
        ParseError {
            error: ParseErrorType::LexError {
                error: LexicalError {
                    error: LexicalErrorType::InvalidUnicodeEscape(
                        InvalidUnicodeEscapeError::InvalidCodepoint,
                    ),
                    location: SrcSpan { start: 1, end: 11 },
                }
            },
            location: SrcSpan { start: 1, end: 11 },
        }
    );
}

#[test]
fn bit_array_too_small_unit() {
    // non int value in bit array unit option
    assert_error!(
        "let x = <<1:unit(0)>> x",
        ParseError {
            error: ParseErrorType::InvalidBitArrayUnit,
            location: SrcSpan { start: 17, end: 18 }
        }
    );
}

proptest! {
    #[test]
    fn bit_array_too_big_unit(n in 257..u32::MAX) {
        let src = format!("let x = <<1:unit({})>> x", n);
        //                                  ^ 17
        assert_error!(
            &src,
            ParseError {
                error: ParseErrorType::InvalidBitArrayUnit,
                location: SrcSpan { start: 17, end: 17 + n.to_string().len() as u32 }
            }
        );
    }
}

#[test]
fn bit_array2() {
    // patterns cannot be nested
    assert_error!(
        "case <<>> { <<<<1>>:bits>> -> 1 }",
        ParseError {
            error: ParseErrorType::NestedBitArrayPattern,
            location: SrcSpan { start: 14, end: 19 }
        }
    );
}

proptest! {
    #[test]
    fn bad_name(name in r#"[a-z][a-z0-9_]*([A-Z][a-zA-Z0-9_]*)+"#) {
        let src = format!("let {} = 1", name);
        //                     ^ 4
        let location = SrcSpan { start: 4, end: 4 + name.len() as u32 };
        assert_error!(
            &src,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::BadName { name },
                        location,
                    }
                },
                location,
            }
        );
    }

    #[test]
    fn bad_discard_name(name in r#"_[a-zA-Z0-9_]*([A-Z][a-zA-Z0-9_]*)+"#) {
        let src = format!("let {} = 1", name);
        //                     ^ 4
        let location = SrcSpan { start: 4, end: 4 + name.len() as u32 };
        assert_error!(
            &src,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::BadDiscardName { name },
                        location,
                    }
                },
                location,
            }
        );
    }

    #[test]
    fn bad_upname(name in r#"[A-Z][a-zA-Z0-9_]*(_[a-zA-Z0-9]*)+"#) {
        let src = format!("type {} = String", name);
        //                      ^ 5
        let location = SrcSpan { start: 5, end: 5 + name.len() as u32 };
        assert_error!(
            &src,
            ParseError {
                error: ParseErrorType::LexError {
                    error: LexicalError {
                        error: LexicalErrorType::BadUpname { name },
                        location,
                    }
                },
                location,
            }
        );
    }
}

// https://github.com/gleam-lang/gleam/issues/1231
#[test]
fn pointless_spread() {
    assert_error!(
        "let xs = [] [..xs]",
        ParseError {
            error: ParseErrorType::ListSpreadWithoutElements,
            location: SrcSpan { start: 12, end: 18 },
        }
    );
}

// https://github.com/gleam-lang/gleam/issues/1358
#[test]
fn lowercase_bool_in_pattern() {
    assert_error!(
        "case 42 > 42 { true -> 1; false -> 2; }",
        ParseError {
            error: ParseErrorType::LowercaseBooleanPattern,
            location: SrcSpan { start: 15, end: 19 },
        }
    );
}

// https://github.com/gleam-lang/gleam/issues/1613
#[test]
fn anonymous_function_labeled_arguments() {
    assert_error!(
        "\
let anon_subtract = fn (minuend a: Int, subtrahend b: Int) -> Int {
  a - b
}",
        ParseError {
            location: SrcSpan { start: 24, end: 31 },
            error: ParseErrorType::UnexpectedLabel
        }
    );
}

#[test]
fn no_let_binding() {
    assert_error!(
        "foo = 32",
        ParseError {
            location: SrcSpan { start: 4, end: 5 },
            error: ParseErrorType::NoLetBinding
        }
    );
}

#[test]
fn no_let_binding1() {
    assert_error!(
        "foo:Int = 32",
        ParseError {
            location: SrcSpan { start: 3, end: 4 },
            error: ParseErrorType::NoLetBinding
        }
    );
}

#[test]
fn no_let_binding2() {
    assert_error!(
        "let bar:Int = 32
        bar = 42",
        ParseError {
            location: SrcSpan { start: 29, end: 30 },
            error: ParseErrorType::NoLetBinding
        }
    );
}

#[test]
fn no_let_binding3() {
    assert_error!(
        "[x] = [2]",
        ParseError {
            location: SrcSpan { start: 4, end: 5 },
            error: ParseErrorType::NoLetBinding
        }
    );
}

#[test]
fn no_eq_after_binding() {
    assert_error!(
        "let foo",
        ParseError {
            location: SrcSpan { start: 4, end: 7 },
            error: ParseErrorType::ExpectedEqual
        }
    );
}

#[test]
fn no_eq_after_binding1() {
    assert_error!(
        "let foo
        foo = 4",
        ParseError {
            location: SrcSpan { start: 4, end: 7 },
            error: ParseErrorType::ExpectedEqual
        }
    );
}

#[test]
fn no_let_binding_snapshot_1() {
    assert_error!("foo = 4");
}

#[test]
fn no_let_binding_snapshot_2() {
    assert_error!("foo:Int = 4");
}

#[test]
fn no_let_binding_snapshot_3() {
    assert_error!(
        "let bar:Int = 32
        bar = 42"
    );
}

#[test]
fn no_eq_after_binding_snapshot_1() {
    assert_error!("let foo");
}
#[test]
fn no_eq_after_binding_snapshot_2() {
    assert_error!(
        "let foo
        foo = 4"
    );
}

#[test]
fn discard_left_hand_side_of_concat_pattern() {
    assert_error!(
        r#"
        case "" {
          _ <> rest -> rest
        }
        "#
    );
}

#[test]
fn assign_left_hand_side_of_concat_pattern() {
    assert_error!(
        r#"
        case "" {
          first <> rest -> rest
        }
        "#
    );
}

// https://github.com/gleam-lang/gleam/issues/1890
#[test]
fn valueless_list_spread_expression() {
    assert_error!(r#"let x = [1, 2, 3, ..]"#);
}

// https://github.com/gleam-lang/gleam/issues/2035
#[test]
fn semicolons() {
    assert_error!(r#"{ 2 + 3; - -5; }"#);
}

#[test]
fn bare_expression() {
    assert_parse!(r#"1"#);
}

// https://github.com/gleam-lang/gleam/issues/1991
#[test]
fn block_of_one() {
    assert_parse!(r#"{ 1 }"#);
}

// https://github.com/gleam-lang/gleam/issues/1991
#[test]
fn block_of_two() {
    assert_parse!(r#"{ 1 2 }"#);
}

// https://github.com/gleam-lang/gleam/issues/1991
#[test]
fn nested_block() {
    assert_parse!(r#"{ 1 { 1.0 2.0 } 3 }"#);
}

// https://github.com/gleam-lang/gleam/issues/1831
#[test]
fn argument_scope() {
    assert_error!(
        "
1 + let a = 5
a
"
    );
}

#[test]
fn multiple_external_for_same_project_erlang() {
    assert_module_error!(
        r#"
@external(erlang, "one", "two")
@external(erlang, "three", "four")
pub fn one(x: Int) -> Int {
  todo
}
"#
    );
}

#[test]
fn multiple_external_for_same_project_javascript() {
    assert_module_error!(
        r#"
@external(javascript, "one", "two")
@external(javascript, "three", "four")
pub fn one(x: Int) -> Int {
  todo
}
"#
    );
}

#[test]
fn unknown_attribute() {
    assert_module_error!(
        r#"@go_faster()
pub fn main() { 1 }"#
    );
}

#[test]
fn incomplete_function() {
    assert_error!("fn()");
}

#[test]
fn multiple_deprecation_attributes() {
    assert_module_error!(
        r#"
@deprecated("1")
@deprecated("2")
pub fn main() -> Nil {
  Nil
}
"#
    );
}

#[test]
fn attributes_with_no_definition() {
    assert_module_error!(
        r#"
@deprecated("1")
@target(erlang)
"#
    );
}

#[test]
fn external_attribute_with_non_fn_definition() {
    assert_module_error!(
        r#"
@external(erlang, "module", "fun")
pub type Fun
"#
    );
}

#[test]
fn attributes_with_improper_definition() {
    assert_module_error!(
        r#"
@deprecated("1")
@external(erlang, "module", "fun")
"#
    );
}

#[test]
fn import_type() {
    assert_parse_module!(r#"import wibble.{type Wobble, Wobble, type Wabble}"#);
}

#[test]
fn reserved_auto() {
    assert_module_error!(r#"const auto = 1"#);
}

#[test]
fn reserved_delegate() {
    assert_module_error!(r#"const delegate = 1"#);
}

#[test]
fn reserved_derive() {
    assert_module_error!(r#"const derive = 1"#);
}

#[test]
fn reserved_else() {
    assert_module_error!(r#"const else = 1"#);
}

#[test]
fn reserved_implement() {
    assert_module_error!(r#"const implement = 1"#);
}

#[test]
fn reserved_macro() {
    assert_module_error!(r#"const macro = 1"#);
}

#[test]
fn reserved_test() {
    assert_module_error!(r#"const test = 1"#);
}

#[test]
fn reserved_echo() {
    assert_module_error!(r#"const echo = 1"#);
}

#[test]
fn capture_with_name() {
    assert_module_error!(
        r#"
pub fn main() {
  add(_name, 1)
}

fn add(x, y) {
  x + y
}
"#
    );
}

#[test]
fn list_spread_with_no_tail_in_the_middle_of_a_list() {
    assert_module_error!(
        r#"
pub fn main() -> Nil {
  let xs = [1, 2, 3]
  [1, 2, .., 3 + 3, 4]
}
"#
    );
}

#[test]
fn list_spread_followed_by_extra_items() {
    assert_module_error!(
        r#"
pub fn main() -> Nil {
  let xs = [1, 2, 3]
  [1, 2, ..xs, 3 + 3, 4]
}
"#
    );
}

// Tests for nested tuples and structs in tuples
// https://github.com/gleam-lang/gleam/issues/1980

#[test]
fn nested_tuples() {
    assert_parse!(
        r#"
let tup = #(#(5, 6))
{tup.0}.1
"#
    );
}

#[test]
fn nested_tuples_no_block() {
    assert_parse!(
        r#"
let tup = #(#(5, 6))
tup.0.1
"#
    );
}

#[test]
fn deeply_nested_tuples() {
    assert_parse!(
        r#"
let tup = #(#(#(#(4))))
{{{tup.0}.0}.0}.0
"#
    );
}

#[test]
fn deeply_nested_tuples_no_block() {
    assert_parse!(
        r#"
let tup = #(#(#(#(4))))
tup.0.0.0.0
"#
    );
}
