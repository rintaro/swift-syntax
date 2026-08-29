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

extension RawSyntax {
  /// A view into the ``RawSyntax`` that exposes functionality that's specific to tokens.
  /// The token's payload must be a token, otherwise this traps.
  @_spi(RawSyntax)
  public var tokenView: RawSyntaxTokenView? {
    switch raw.header {
    case .smolParsedToken, .parsedToken, .materializedToken:
      return RawSyntaxTokenView(raw: self)
    case .layout:
      return nil
    }
  }
}

/// A view into ``RawSyntax`` that exposes functionality that only applies to tokens.
@_spi(RawSyntax)
public struct RawSyntaxTokenView: Sendable {
  let raw: RawSyntax

  fileprivate init(raw: RawSyntax) {
    self.raw = raw
    switch raw.header {
    case .smolParsedToken, .parsedToken, .materializedToken:
      break
    case .layout:
      preconditionFailure("RawSyntax must be a token")
    }
  }

  /// Token kind of this node.
  @_spi(RawSyntax)
  public var rawKind: RawTokenKind {
    switch raw.header {
    case .smolParsedToken:
      return raw.smolParsedToken.pointee.tokenKind
    case .parsedToken:
      return raw.parsedToken.pointee.tokenKind
    case .materializedToken:
      return raw.materializedToken.pointee.tokenKind
    case .layout:
      preconditionFailure("'tokenKind' is not available for non-token node")
    }
  }

  /// Token text of this node.
  @_spi(RawSyntax)
  public var rawText: SyntaxText {
    switch raw.header {
    case .smolParsedToken:
      return raw.smolParsedToken.pointee.tokenText(base: raw.smolParsedTokenTextBase)
    case .parsedToken:
      return raw.parsedToken.pointee.tokenText(base: raw.parsedTokenTextBase)
    case .materializedToken:
      return raw.materializedToken.pointee.tokenText
    case .layout:
      preconditionFailure("'rawText' is not available for non-token node")
    }
  }

  /// The UTF-8 byte length of the leading trivia.
  @_spi(RawSyntax)
  public var leadingTriviaByteLength: Int {
    switch raw.header {
    case .smolParsedToken:
      return raw.smolParsedToken.pointee.leadingTriviaText(base: raw.smolParsedTokenTextBase).count
    case .parsedToken:
      return raw.parsedToken.pointee.leadingTriviaText(base: raw.parsedTokenTextBase).count
    case .materializedToken:
      return raw.materializedToken.pointee.leadingTrivia.reduce(0) { $0 + $1.byteLength }
    case .layout:
      preconditionFailure("'leadingTriviaByteLength' is not available for non-token node")
    }
  }

  /// The UTF-8 byte length of the trailing trivia.
  @_spi(RawSyntax)
  public var trailingTriviaByteLength: Int {
    switch raw.header {
    case .smolParsedToken:
      return raw.smolParsedToken.pointee.trailingTriviaText(base: raw.smolParsedTokenTextBase).count
    case .parsedToken:
      return raw.parsedToken.pointee.trailingTriviaText(base: raw.parsedTokenTextBase).count
    case .materializedToken:
      return raw.materializedToken.pointee.trailingTrivia.reduce(0) { $0 + $1.byteLength }
    case .layout:
      preconditionFailure("'trailingTriviaByteLength' is not available for non-token node")
    }
  }

  @_spi(RawSyntax)
  public var leadingRawTriviaPieces: [RawTriviaPiece] {
    switch raw.header {
    case .smolParsedToken:
      return raw.arenaReference.parseTrivia(
        source: raw.smolParsedToken.pointee.leadingTriviaText(base: raw.smolParsedTokenTextBase),
        position: .leading
      )
    case .parsedToken:
      return raw.arenaReference.parseTrivia(
        source: raw.parsedToken.pointee.leadingTriviaText(base: raw.parsedTokenTextBase),
        position: .leading
      )
    case .materializedToken:
      return Array(raw.materializedToken.pointee.leadingTrivia)
    case .layout:
      preconditionFailure("'leadingRawTriviaPieces' is called on non-token raw syntax")
    }
  }

  @_spi(RawSyntax)
  public var trailingRawTriviaPieces: [RawTriviaPiece] {
    switch raw.header {
    case .smolParsedToken:
      return raw.arenaReference.parseTrivia(
        source: raw.smolParsedToken.pointee.trailingTriviaText(base: raw.smolParsedTokenTextBase),
        position: .trailing
      )
    case .parsedToken:
      return raw.arenaReference.parseTrivia(
        source: raw.parsedToken.pointee.trailingTriviaText(base: raw.parsedTokenTextBase),
        position: .trailing
      )
    case .materializedToken:
      return Array(raw.materializedToken.pointee.trailingTrivia)
    case .layout:
      preconditionFailure("'trailingRawTriviaPieces' is called on non-token raw syntax")
    }
  }

  /// Returns the leading ``Trivia`` length.
  @_spi(RawSyntax)
  public var leadingTriviaLength: SourceLength {
    return SourceLength(utf8Length: leadingTriviaByteLength)
  }

  /// Returns the trailing ``Trivia`` length.
  @_spi(RawSyntax)
  public var trailingTriviaLength: SourceLength {
    return SourceLength(utf8Length: trailingTriviaByteLength)
  }

  /// Run `body` with text of the leading trivia and return its result.
  @_spi(RawSyntax)
  public func leadingTrivia<T>(_ body: (SyntaxText) -> T) -> T {
    switch raw.header {
    case .smolParsedToken:
      return body(raw.smolParsedToken.pointee.leadingTriviaText(base: raw.smolParsedTokenTextBase))
    case .parsedToken:
      return body(raw.parsedToken.pointee.leadingTriviaText(base: raw.parsedTokenTextBase))
    case .materializedToken:
      var leadingTriviaStr = Trivia(pieces: raw.materializedToken.pointee.leadingTrivia.map(TriviaPiece.init))
        .description
      return leadingTriviaStr.withSyntaxText(body)
    case .layout:
      preconditionFailure("'leadingTrivia' is called on non-token raw syntax")
    }
  }

  /// Run `body` with text of the leading trivia and return its result.
  @_spi(RawSyntax)
  public func trailingTrivia<T>(_ body: (SyntaxText) -> T) -> T {
    switch raw.header {
    case .smolParsedToken:
      return body(raw.smolParsedToken.pointee.trailingTriviaText(base: raw.smolParsedTokenTextBase))
    case .parsedToken:
      return body(raw.parsedToken.pointee.trailingTriviaText(base: raw.parsedTokenTextBase))
    case .materializedToken:
      var trailingTriviaStr = Trivia(pieces: raw.materializedToken.pointee.trailingTrivia.map(TriviaPiece.init))
        .description
      return trailingTriviaStr.withSyntaxText(body)
    case .layout:
      preconditionFailure("'trailingTrivia' is called on non-token raw syntax")
    }
  }

  /// Returns the leading ``Trivia``.
  @_spi(RawSyntax)
  public func formLeadingTrivia() -> Trivia {
    return Trivia(pieces: leadingRawTriviaPieces.map({ TriviaPiece(raw: $0) }))
  }

  /// Returns the trailing ``Trivia``.
  /// - Returns: nil if called on a layout node.
  @_spi(RawSyntax)
  public func formTrailingTrivia() -> Trivia {
    return Trivia(pieces: trailingRawTriviaPieces.map({ TriviaPiece(raw: $0) }))
  }

  /// Returns a ``RawSyntax`` node with the same source text but with the token
  /// kind changed to `newValue`.
  @_spi(RawSyntax)
  public func withKind(_ newValue: TokenKind, arena: RawSyntaxArena) -> RawSyntax {
    arena.addChild(self.raw.arenaReference)
    switch raw.header {
    case .smolParsedToken, .parsedToken:
      // The wholeText can't be continuous anymore. Make a materialized token.
      return .makeMaterializedToken(
        kind: newValue,
        leadingTrivia: formLeadingTrivia(),
        trailingTrivia: formTrailingTrivia(),
        presence: presence,
        tokenDiagnostic: tokenDiagnostic,
        arena: arena
      )
    case .materializedToken:
      let decomposed = newValue.decomposeToRaw()
      let rawKind = decomposed.rawKind
      let text: SyntaxText = (decomposed.string.map({ arena.intern($0) }) ?? decomposed.rawKind.defaultText ?? "")
      // Mutate a copy. This returns a modified token and leaves the one it was
      // called on alone, and with the fields behind a pointer, writing through it
      // would instead change that token for every node holding it.
      var materialized = raw.materializedToken.pointee
      materialized.tokenKind = rawKind
      materialized.tokenText = text
      return RawSyntax(arena: arena, materializedToken: materialized)
    default:
      preconditionFailure("'withKind()' is called on non-token raw syntax")
    }
  }

  /// Returns a ``RawSyntax`` node with the presence changed to `newValue`.
  /// A parsed token like this one, with `presence` and `tokenDiagnostic` as
  /// given, allocated in `arena`.
  ///
  /// Where `arena` is not the one this token lives in, the result has to be a
  /// materialized token: a parsed token keeps its trivia unparsed and asks its
  /// arena to parse it on demand, so it can only live in a
  /// `ParsingRawSyntaxArena`, and another one's function may differ or be
  /// absent. Copying the text into the node settles who owns the bytes, not who
  /// parses them.
  private func rebuiltParsedToken(
    tokenKind: RawTokenKind,
    wholeText: SyntaxText,
    textRange: Range<SyntaxText.Index>,
    presence: SourcePresence,
    tokenDiagnostic: TokenDiagnostic?,
    arena: RawSyntaxArena
  ) -> RawSyntax {
    guard arena == self.raw.arenaReference else {
      return .makeMaterializedToken(
        kind: formKind(),
        leadingTrivia: formLeadingTrivia(),
        trailingTrivia: formTrailingTrivia(),
        presence: presence,
        tokenDiagnostic: tokenDiagnostic,
        arena: arena
      )
    }
    return RawSyntax(
      arena: arena,
      parsedToken: RawSyntaxData.ParsedToken(
        tokenKind: tokenKind,
        wholeTextLength: wholeText.count,
        textRange: textRange,
        presence: presence,
        tokenDiagnostic: tokenDiagnostic
      ),
      wholeText: wholeText
    )
  }

  @_spi(RawSyntax)
  public func withPresence(_ newValue: SourcePresence, arena: RawSyntaxArena) -> RawSyntax {
    arena.addChild(self.raw.arenaReference)
    switch raw.header {
    case .smolParsedToken:
      let fields = raw.smolParsedToken.pointee
      return rebuiltParsedToken(
        tokenKind: fields.tokenKind,
        wholeText: fields.wholeText(base: raw.smolParsedTokenTextBase),
        textRange: fields.textRange,
        presence: newValue,
        tokenDiagnostic: nil,
        arena: arena
      )
    case .parsedToken:
      let fields = raw.parsedToken.pointee
      return rebuiltParsedToken(
        tokenKind: fields.tokenKind,
        wholeText: fields.wholeText(base: raw.parsedTokenTextBase),
        textRange: fields.textRange,
        presence: newValue,
        tokenDiagnostic: fields.tokenDiagnostic,
        arena: arena
      )
    case .materializedToken:
      var materialized = raw.materializedToken.pointee
      materialized.presence = newValue
      return RawSyntax(arena: arena, materializedToken: materialized)
    default:
      preconditionFailure("'withKind()' is called on non-token raw syntax")
    }
  }

  /// The length of the token without leading or trailing trivia, assuming this
  /// is a token node.
  @_spi(RawSyntax)
  public var textByteLength: Int {
    switch raw.header {
    case .smolParsedToken:
      return raw.smolParsedToken.pointee.tokenText(base: raw.smolParsedTokenTextBase).count
    case .parsedToken:
      return raw.parsedToken.pointee.tokenText(base: raw.parsedTokenTextBase).count
    case .materializedToken:
      return raw.materializedToken.pointee.tokenText.count
    case .layout:
      preconditionFailure("'textByteLength' is not available for non-token node")
    }
  }

  @_spi(RawSyntax)
  public var trimmedLength: SourceLength {
    SourceLength(utf8Length: textByteLength)
  }

  @_spi(RawSyntax)
  public func formKind() -> TokenKind {
    switch raw.header {
    case .smolParsedToken:
      return TokenKind.fromRaw(
        kind: raw.smolParsedToken.pointee.tokenKind,
        text: String(syntaxText: raw.smolParsedToken.pointee.tokenText(base: raw.smolParsedTokenTextBase))
      )
    case .parsedToken:
      return TokenKind.fromRaw(
        kind: raw.parsedToken.pointee.tokenKind,
        text: String(syntaxText: raw.parsedToken.pointee.tokenText(base: raw.parsedTokenTextBase))
      )
    case .materializedToken:
      return TokenKind.fromRaw(
        kind: raw.materializedToken.pointee.tokenKind,
        text: String(syntaxText: raw.materializedToken.pointee.tokenText)
      )
    case .layout:
      preconditionFailure("'formKind' is not available for non-token node")
    }
  }

  @_spi(RawSyntax)
  public var presence: SourcePresence {
    switch raw.header {
    case .smolParsedToken:
      return .present
    case .parsedToken:
      return raw.parsedToken.pointee.presence
    case .materializedToken:
      return raw.materializedToken.pointee.presence
    case .layout:
      preconditionFailure("'presence' is not available for non-token node")
    }
  }

  @_spi(RawSyntax)
  public var tokenDiagnostic: TokenDiagnostic? {
    switch raw.header {
    case .smolParsedToken:
      return nil
    case .parsedToken:
      return raw.parsedToken.pointee.tokenDiagnostic
    case .materializedToken:
      return raw.materializedToken.pointee.tokenDiagnostic
    case .layout:
      preconditionFailure("'tokenDiagnostic' is not available for non-token node")
    }
  }

  @_spi(RawSyntax)
  public func withTokenDiagnostic(tokenDiagnostic: TokenDiagnostic?, arena: RawSyntaxArena) -> RawTokenSyntax {
    arena.addChild(self.raw.arenaReference)
    switch raw.header {
    case .smolParsedToken:
      let fields = raw.smolParsedToken.pointee
      return rebuiltParsedToken(
        tokenKind: fields.tokenKind,
        wholeText: fields.wholeText(base: raw.smolParsedTokenTextBase),
        textRange: fields.textRange,
        presence: .present,
        tokenDiagnostic: tokenDiagnostic,
        arena: arena
      ).cast(RawTokenSyntax.self)
    case .parsedToken:
      let fields = raw.parsedToken.pointee
      return rebuiltParsedToken(
        tokenKind: fields.tokenKind,
        wholeText: fields.wholeText(base: raw.parsedTokenTextBase),
        textRange: fields.textRange,
        presence: fields.presence,
        tokenDiagnostic: tokenDiagnostic,
        arena: arena
      ).cast(RawTokenSyntax.self)
    case .materializedToken:
      var materialized = raw.materializedToken.pointee
      materialized.tokenDiagnostic = tokenDiagnostic
      return RawSyntax(arena: arena, materializedToken: materialized)
        .cast(RawTokenSyntax.self)
    default:
      preconditionFailure("'withTokenDiagnostic' is not available for non-token node")
    }
  }
}
