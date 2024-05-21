// Copyright 2015-2019 Parity Technologies (UK) Ltd.
// This file is part of Parity Ethereum.

// Parity Ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Ethereum.  If not, see <http://www.gnu.org/licenses/>.

//! Solidity type-name parsing
use crate::error::*;
use std::{fmt, result};

use chumsky::{prelude::*, text::ident};

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    BracketOpen,
    BracketClose,
    Identifier(String),
    LiteralInteger(String),
    TypeBool,
    TypeAddress,
    TypeString,
    TypeByte(String),
    TypeBytes,
    TypeInt,
    TypeUint,
}

fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let digits = text::digits::<_, Simple<char>>(10);
    let identifier = ident().map(Token::Identifier);
    let uint = just("uint").to(Token::TypeUint);
    let int = just("int").to(Token::TypeInt);
    let string = just("string").to(Token::TypeString);
    let bool_ = just("bool").to(Token::TypeBool);
    let bytes = just("bytes").to(Token::TypeBytes);
    let address = just("address").to(Token::TypeAddress);
    let number = digits.clone().map(Token::LiteralInteger);
    let byte = just("byte").then(digits).map(|(_, n)| Token::TypeByte(n));
    let bracket_open = just('[').to(Token::BracketOpen);
    let bracket_close = just(']').to(Token::BracketClose);

    let token = uint
        .or(int)
        .or(string)
        .or(bool_)
        .or(bytes)
        .or(address)
        .or(byte)
        .or(number)
        .or(bracket_open)
        .or(bracket_close)
        .or(identifier);

    token.padded().repeated().then_ignore(end())
}

fn tokenize(input: &str) -> Result<Vec<Token>> {
    lexer()
        .parse(input)
        .map_err(|err| ErrorKind::LexerError(format!("{err:?}")).into())
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Address,
    Uint,
    Int,
    String,
    Bool,
    Bytes,
    Byte(u8),
    Custom(String),
    Array {
        length: Option<u64>,
        inner: Box<Type>,
    },
}

impl From<Type> for String {
    fn from(field_type: Type) -> String {
        match field_type {
            Type::Address => "address".into(),
            Type::Uint => "uint".into(),
            Type::Int => "int".into(),
            Type::String => "string".into(),
            Type::Bool => "bool".into(),
            Type::Bytes => "bytes".into(),
            Type::Byte(len) => format!("bytes{}", len),
            Type::Custom(custom) => custom,
            Type::Array { inner, length } => {
                let inner: String = (*inner).into();
                match length {
                    None => format!("{}[]", inner),
                    Some(length) => format!("{}[{}]", inner, length),
                }
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        let item: String = self.clone().into();
        write!(f, "{}", item)
    }
}

/// the type string is being validated before it's parsed.
pub fn parse_type(field_type: &str) -> Result<Type> {
    #[derive(PartialEq)]
    enum State {
        Open,
        Close,
    }

    let tokens = tokenize(field_type)?;
    // let mut lexer = Lexer::new(field_type);
    let mut token = None;
    let mut state = State::Close;
    let mut array_depth = 0;
    let mut current_array_length: Option<u64> = None;

    for tk in tokens {
        let type_ = match tk {
            Token::Identifier(ident) => Type::Custom(ident),
            Token::TypeByte(n) => {
                Type::Byte(n.parse().map_err(|_| ErrorKind::InvalidArraySize(n))?)
            }
            Token::TypeBytes => Type::Bytes,
            Token::TypeBool => Type::Bool,
            Token::TypeUint => Type::Uint,
            Token::TypeInt => Type::Int,
            Token::TypeString => Type::String,
            Token::TypeAddress => Type::Address,
            Token::LiteralInteger(length) => {
                current_array_length = Some(
                    length
                        .parse()
                        .map_err(|_| ErrorKind::InvalidArraySize(length.into()))?,
                );
                continue;
            }
            Token::BracketOpen if token.is_some() && state == State::Close => {
                state = State::Open;
                continue;
            }
            Token::BracketClose if array_depth < 10 => {
                if state == State::Open && token.is_some() {
                    let length = current_array_length.take();
                    state = State::Close;
                    token = Some(Type::Array {
                        inner: Box::new(token.expect("if statement checks for some; qed")),
                        length,
                    });
                    array_depth += 1;
                    continue;
                } else {
                    return Err(ErrorKind::UnexpectedToken(
                        format!("{token:?}"),
                        field_type.to_owned(),
                    ))?;
                }
            }
            Token::BracketClose if array_depth == 10 => {
                return Err(ErrorKind::UnsupportedArrayDepth)?;
            }
            _ => {
                return Err(ErrorKind::UnexpectedToken(
                    format!("{token:?}"),
                    field_type.to_owned(),
                ))?
            }
        };
        token = Some(type_);
    }

    Ok(token.ok_or(ErrorKind::NonExistentType)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser() {
        let source = "byte[][][7][][][][][][][]";
        parse_type(source).unwrap();
    }

    #[test]
    fn test_nested_array() {
        let source = "byte[][][7][][][][][][][][]";
        assert_eq!(parse_type(source).is_err(), true);
    }

    #[test]
    fn test_malformed_array_type() {
        let source = "byte[7[]uint][]";
        assert_eq!(parse_type(source).is_err(), true)
    }
}
