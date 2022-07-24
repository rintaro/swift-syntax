//===---------- SyntaxOtherNodes.swift - Syntax Node definitions ----------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2022 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

// MARK: UnknownSyntax

public struct UnknownSyntax: SyntaxProtocol, Hashable {
  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    syntaxKind == .unknown
  }
  public let syntax: Syntax
  @usableFromInline
  init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }
}

extension UnknownSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [:])
  }
}

// MARK: TokenSyntax

/// A Syntax node representing a single token.
///
/// Token syntax is the "leaf" node in the syntax tree. It holds a chunk of the
/// actual source code the syntax tree represents.
public struct TokenSyntax: SyntaxProtocol, Hashable {
  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    return syntaxKind == .token
  }
  public let syntax: Syntax
  @usableFromInline
  init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard other.syntaxKind == .token else { return nil }
    self.init(data: other.data)
  }

  public var isMissing: Bool {
    raw.isMissing
  }

  public var isPresent: Bool {
    !isMissing
  }

  public var presence: SourcePresence {
    return raw.isMissing ? .missing : .present
  }

  public var tokenKind: TokenKind {
    get { raw.tokenKind }
    set { self = withKind(newValue) }
  }

  public func withUnsafeTokenText<T>(_ body: (StringRef) -> T) -> T {
    body(raw.tokenText!)
  }

  public func withUnsafeLeadingTriviaText<T>(_ body: (StringRef) -> T) -> T {
    raw.leadingTrivia!.withUnsafeText(body)
  }

  public func withUnsafeTrailingTriviaText<T>(_ body: (StringRef) -> T) -> T {
    raw.trailingTrivia!.withUnsafeText(body)
  }

  /// The text of the token as written in the source code.
  public var text: String {
    get { String(stringRef: raw.tokenText!) }
    set { self = withTokenText(newValue) }
  }

  public var leadingTriviaText: String {
    get { String(describing: raw.tokenLeadingTrivia!) }
    set { self = withLeadingTriviaText(newValue) }
  }

  public var trailingTriviaText: String {
    get { String(describing: raw.tokenTrailingTrivia!) }
    set { self = withTrailingTriviaText(newValue) }
  }

  public var leadingTriviaLength: Int {
    raw.tokenLeadingTriviaLength
  }

  public var trailingTriviaLength: Int {
    raw.tokenTrailingTriviaLength
  }

  public var leadingTrivia: Trivia {
    get { Trivia.make(arena: raw.arena, raw: raw.tokenLeadingTrivia!) }
    set { self = withLeadingTrivia(newValue) }
  }

  public var trailingTrivia: Trivia {
    get { Trivia.make(arena: raw.arena, raw: raw.tokenTrailingTrivia!) }
    set { self = withTrailingTrivia(newValue) }
  }

  public func withKind(_ newValue: TokenKind) -> TokenSyntax {
    let newRaw = raw.withTokenKind(newValue)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public func withTokenText(_ newValue: String) -> TokenSyntax {
    let newRaw = raw.withTokenText(newValue)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public func withLeadingTriviaText(_ newValue: String) -> TokenSyntax {
    let newRaw = RawSyntax.makeParsedToken(
      arena: arena, kind: tokenKind, text: text,
      leadingTrivia: newValue, trailingTrivia: trailingTriviaText)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public func withTrailingTriviaText(_ newValue: String) -> TokenSyntax {
    let newRaw = RawSyntax.makeParsedToken(
      arena: arena, kind: tokenKind, text: text,
      leadingTrivia: leadingTriviaText, trailingTrivia: newValue)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public func withLeadingTrivia(_ newValue: Trivia) -> TokenSyntax {
    let newRaw = RawSyntax.makeMaterializedToken(
      arena: arena, kind: raw.tokenKind, text: text,
      leadingTrivia: newValue, trailingTrivia: trailingTrivia)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public func withTrailingTrivia(_ newValue: Trivia) -> TokenSyntax {
    let newRaw = RawSyntax.makeMaterializedToken(
      arena: arena, kind: raw.tokenKind, text: text,
      leadingTrivia: leadingTrivia, trailingTrivia: newValue)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension TokenSyntax: CustomReflectable {
  public var customMirror: Mirror {
    Mirror(self, children: [
      "text": text,
      "leadingTrivia": leadingTrivia,
      "trailingTrivia": trailingTrivia,
      "tokenKind": tokenKind,
    ])
  }
}
