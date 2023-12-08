//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2023 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

@_spi(RawSyntax) import SwiftSyntax

/// Describes a token that should be consumed by the parser.
///
/// All the methods in here and all functions that take a ``TokenSpec`` need to be
/// marked `@inline(__always)` so the compiler inlines the ``RawTokenKind`` we are
/// matching against and is thus able to rule out one of the branches in
/// `matches(rawTokenKind:text:)` based on the matched kind.
@_spi(AlternateTokenIntrospection)
public struct TokenSpec {
  /// The kind we expect the token that we want to consume to have.
  /// This can be a keyword, in which case the ``TokenSpec`` will also match an
  /// identifier with the same text as the keyword and remap it to that keyword
  /// when consumed.
  ///
  /// `fileprivate` because only functions in this file should access it since
  /// they know how to handle the identifier -> keyword remapping.
  fileprivate let rawTokenKind: RawTokenKind

  /// If not nil, the token will be remapped to the provided kind when consumed.
  ///
  /// `fileprivate` because only functions in this file should access it since
  /// they know how to handle the identifier -> keyword remapping.
  fileprivate let remapping: RawTokenKind?

  /// The recovery precedence that should be used when consuming this token. By
  /// default this is the token precedence of `rawTokenKind` but it can be
  /// overridden.
  let recoveryPrecedence: TokenPrecedence

  /// Whether the token is allowed to be at the start of a line. Defaults to
  /// `true` but can be set to `false` to consume a token for recovery purposes
  /// that is not allowed to start a new line.
  let allowAtStartOfLine: Bool

  @inline(__always)
  init(
    _ rawTokenKind: RawTokenKind,
    remapping: RawTokenKind? = nil,
    recoveryPrecedence: TokenPrecedence? = nil,
    allowAtStartOfLine: Bool = true
  ) {
    self.rawTokenKind = rawTokenKind
    self.remapping = remapping
    self.recoveryPrecedence = recoveryPrecedence ?? TokenPrecedence(rawTokenKind)
    self.allowAtStartOfLine = allowAtStartOfLine
  }

  @inline(__always)
  func matches(
    rawTokenKind: RawTokenKind,
    rawTokenText: SyntaxText,
    atStartOfLine: @autoclosure () -> Bool
  ) -> Bool {
    if !allowAtStartOfLine && atStartOfLine() {
      return false
    }
    if rawTokenKind == self.rawTokenKind {
      return true
    }
    if rawTokenKind == .identifier && self.rawTokenKind.isKeywordKind && rawTokenText == self.rawTokenKind.defaultText {
      return true
    }
    return false
  }

  @inline(__always)
  static func ~= (kind: TokenSpec, lexeme: Lexer.Lexeme) -> Bool {
    return kind.matches(
      rawTokenKind: lexeme.rawTokenKind,
      rawTokenText: lexeme.tokenText,
      atStartOfLine: lexeme.isAtStartOfLine
    )
  }

  @inline(__always)
  static func ~= (kind: TokenSpec, token: TokenSyntax) -> Bool {
    return kind.matches(
      rawTokenKind: token.tokenView.rawKind,
      rawTokenText: token.tokenView.rawText,
      atStartOfLine: token.leadingTrivia.contains(where: { $0.isNewline })
    )
  }

  @inline(__always)
  static func ~= (kind: TokenSpec, token: RawTokenSyntax) -> Bool {
    return kind.matches(
      rawTokenKind: token.tokenKind,
      rawTokenText: token.tokenText,
      atStartOfLine: token.leadingTriviaPieces.contains(where: \.isNewline)
    )
  }

  /// Returns a ``TokenKind`` that will most likely be parsed as a token that
  /// matches this ``TokenSpec``.
  ///
  /// IMPORTANT: Should only be used when generating tokens during the
  /// modification of test cases. This should never be used in the parser itself.
  @_spi(AlternateTokenIntrospection)
  public var synthesizedTokenKind: TokenKind {
    switch rawTokenKind {
    case .binaryOperator: return .binaryOperator("+")
    case .dollarIdentifier: return .dollarIdentifier("$0")
    case .floatLiteral: return .floatLiteral("1.0")
    case .identifier: return .identifier("myIdent")
    case .integerLiteral: return .integerLiteral("1")
    case .postfixOperator: return .postfixOperator("++")
    case .prefixOperator: return .prefixOperator("!")
    case .rawStringPoundDelimiter: return .rawStringPoundDelimiter("#")
    case .regexLiteralPattern: return .regexLiteralPattern(".*")
    case .regexPoundDelimiter: return .regexPoundDelimiter("#")
    case .stringSegment: return .stringSegment("abc")
    default: return TokenKind.fromRaw(kind: rawTokenKind, text: "")
    }
  }
}

extension TokenConsumer {
  /// Generates a missing token that has the expected kind of `spec`.
  @inline(__always)
  mutating func missingToken(_ spec: TokenSpec) -> Token {
    return missingToken(spec.remapping ?? spec.rawTokenKind, text: spec.rawTokenKind.defaultText)
  }

  /// Asserts that the current token matches `spec` and consumes it, performing
  /// any necessary token kind remapping.
  ///
  /// This should only be called from parsing primitives like `consume(if:)` and
  /// `eat`. Introduce new users of this very sparingly.
  @inline(__always)
  mutating func eat(_ spec: TokenSpec) -> Token {
    precondition(spec ~= self.currentToken)
    return self.consumeAnyToken(remapping: spec.remapping ?? spec.rawTokenKind)
  }
}
