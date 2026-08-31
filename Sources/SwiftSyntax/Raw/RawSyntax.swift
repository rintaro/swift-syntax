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

@_spi(RawSyntax) public typealias RawSyntaxBuffer = ArenaAllocatedBufferPointer<RawSyntax?>

typealias RawTriviaPieceBuffer = ArenaAllocatedBufferPointer<RawTriviaPiece>

fileprivate extension SyntaxKind {
  /// Whether this node kind should be considered as `hasError` for purposes of `RecursiveRawSyntaxFlags`.
  var hasError: Bool {
    return self == .unexpectedNodes || self.isMissing
  }
}

struct RecursiveRawSyntaxFlags: OptionSet, Sendable {
  let rawValue: UInt8

  /// Whether the tree contained by this layout has any
  ///  - missing nodes or
  ///  - unexpected nodes or
  ///  - tokens with a ``TokenDiagnostic`` of severity `error`
  static let hasError = RecursiveRawSyntaxFlags(rawValue: 1 << 0)
  /// Whether the tree contained by this layout has any tokens with a
  /// ``TokenDiagnostic`` of severity `warning`.
  static let hasWarning = RecursiveRawSyntaxFlags(rawValue: 1 << 1)
  static let hasSequenceExpr = RecursiveRawSyntaxFlags(rawValue: 1 << 2)
  static let hasMaximumNestingLevelOverflow = RecursiveRawSyntaxFlags(rawValue: 1 << 3)
}

/// Node data for RawSyntax tree. Tagged union plus common data.
/// The first word of every syntax node: which of the five shapes it has, and the
/// arena that owns it.
///
/// An enum rather than a struct with a separate tag, because the tag then lives
/// in the spare bits of the reference and the whole thing is one word. A struct
/// holding the same two things is nine bytes, sixteen with padding.
///
/// Each case's fields are tail allocated after this word, in the shape named
/// after it below. No value of those shapes is ever made: they describe memory
/// that the node owns.
internal enum RawSyntaxData: Sendable {
  case smolParsedToken(RawSyntaxArenaRef)
  case parsedToken(RawSyntaxArenaRef)
  case materializedToken(RawSyntaxArenaRef)
  /// A node whose children are all elements of one kind, with no `unexpected`
  /// slots between them. Its fields have the shape of `Layout`.
  case collection(RawSyntaxArenaRef)
  /// A layout node holding only its real children, which is every layout node
  /// that parsed without anything unexpected in it. Its fields have the shape of
  /// `Layout`, followed by `childCount` slots.
  case layout(RawSyntaxArenaRef)
  /// A layout node that has something in at least one of its `unexpected` slots,
  /// so it holds them after its real children: `childCount` slots and then
  /// `childCount + 1` of them.
  case layoutWithUnexpected(RawSyntaxArenaRef)

  var arenaReference: RawSyntaxArenaRef {
    switch self {
    case .smolParsedToken(let ref), .parsedToken(let ref), .materializedToken(let ref), .collection(let ref),
      .layout(let ref), .layoutWithUnexpected(let ref):
      return ref
    }
  }

  /// Short, present, undiagnosed parsed token.
  struct SmolParsedToken: Sendable {
    var wholeTextLength: UInt8
    var textLowerBound: UInt8
    var textUpperBound: UInt8
    var tokenKind: RawTokenKind

    var textRange: Range<SyntaxText.Index> {
      Int(self.textLowerBound)..<Int(self.textUpperBound)
    }

    /// The largest text a token of this shape can hold.
    static let maximumTextLength = Int(UInt8.max)
  }

  /// Token with lazy trivia parsing.
  ///
  /// The RawSyntax's `arena` must have a valid trivia parsing function to
  /// lazily materialize the leading/trailing trivia pieces.
  struct ParsedToken: Sendable {
    /// Byte count of this token's whole text, including leading and trailing
    /// trivia, which is tail allocated immediately after these fields.
    ///
    /// A length rather than a `SyntaxText`: the text begins at a known offset
    /// from the node, so a base address here would repeat what the node's own
    /// address says, at eight bytes for every token in the tree.
    var wholeTextLength: UInt32

    var tokenKind: RawTokenKind

    /// Range of the actual token’s text.
    ///
    /// Text in `wholeText` before `textRange.lowerBound` is leading trivia and
    /// after `textRange.upperBound` is trailing trivia.
    ///
    /// Held as 32-bit offsets: these index within a single token, so an `Int`
    /// apiece is 8 bytes spent on a range no token can reach.
    var textRange: Range<SyntaxText.Index> {
      return Int(self.textLowerBound)..<Int(self.textUpperBound)
    }

    private var textLowerBound: UInt32
    private var textUpperBound: UInt32

    var presence: SourcePresence

    /// Store the members of ``TokenDiagnostic`` individually so the compiler can pack
    /// `ParsedToken` more efficiently (saving 2 bytes)
    /// `tokenDiagnosticByteOffset` is ignored if `tokenDiagnosticKind` is `nil`
    private var tokenDiagnosticKind: TokenDiagnostic.Kind?
    private var tokenDiagnosticByteOffset: UInt16

    var tokenDiagnostic: TokenDiagnostic? {
      get {
        if let kind = tokenDiagnosticKind {
          return TokenDiagnostic(kind, byteOffset: tokenDiagnosticByteOffset)
        } else {
          return nil
        }
      }
      set {
        if let newValue {
          self.tokenDiagnosticKind = newValue.kind
          self.tokenDiagnosticByteOffset = newValue.byteOffset
        } else {
          self.tokenDiagnosticKind = nil
          self.tokenDiagnosticByteOffset = 0
        }
      }
    }

    init(
      tokenKind: RawTokenKind,
      wholeTextLength: Int,
      textRange: Range<SyntaxText.Index>,
      presence: SourcePresence,
      tokenDiagnostic: TokenDiagnostic?
    ) {
      self.tokenKind = tokenKind
      self.wholeTextLength = UInt32(wholeTextLength)
      // Converting to `UInt32` is the bounds check. See `Layout.init`.
      self.textLowerBound = UInt32(textRange.lowerBound)
      self.textUpperBound = UInt32(textRange.upperBound)
      self.presence = presence
      self.tokenDiagnosticKind = tokenDiagnostic?.kind
      self.tokenDiagnosticByteOffset = tokenDiagnostic?.byteOffset ?? 0
    }
  }

  /// Token typically created with `TokenSyntax.<someToken>`.
  struct MaterializedToken: Sendable {
    var tokenKind: RawTokenKind
    var tokenText: SyntaxText
    var triviaPieces: RawTriviaPieceBuffer
    var numLeadingTrivia: UInt32
    var byteLength: UInt32
    var presence: SourcePresence
    /// Store the members of ``TokenDiagnostic`` individually so the compiler can pack
    /// `ParsedToken` more efficiently (saving 2 bytes)
    /// `tokenDiagnosticByteOffset` is ignored if `tokenDiagnosticKind` is `nil`
    private var tokenDiagnosticKind: TokenDiagnostic.Kind?
    private var tokenDiagnosticByteOffset: UInt16

    init(
      tokenKind: RawTokenKind,
      tokenText: SyntaxText,
      triviaPieces: RawTriviaPieceBuffer,
      numLeadingTrivia: UInt32,
      byteLength: UInt32,
      presence: SourcePresence,
      tokenDiagnostic: TokenDiagnostic?
    ) {
      self.tokenKind = tokenKind
      self.tokenText = tokenText
      self.triviaPieces = triviaPieces
      self.numLeadingTrivia = numLeadingTrivia
      self.byteLength = byteLength
      self.presence = presence
      self.tokenDiagnosticKind = tokenDiagnostic?.kind
      self.tokenDiagnosticByteOffset = tokenDiagnostic?.byteOffset ?? 0
    }

    var tokenDiagnostic: TokenDiagnostic? {
      get {
        if let kind = tokenDiagnosticKind {
          return TokenDiagnostic(kind, byteOffset: tokenDiagnosticByteOffset)
        } else {
          return nil
        }
      }
      set {
        if let newValue {
          self.tokenDiagnosticKind = newValue.kind
          self.tokenDiagnosticByteOffset = newValue.byteOffset
        } else {
          self.tokenDiagnosticKind = nil
          self.tokenDiagnosticByteOffset = 0
        }
      }
    }
  }

  /// Layout node including collections.
  ///
  /// The actual layout buffer is tail allocated.
  struct Layout: Sendable {
    var childCount: UInt32
    var byteLength: UInt32
    var descendantCount: UInt32
    var kind: SyntaxKind
    var recursiveFlags: RecursiveRawSyntaxFlags
  }
}

/// Reads a parsed token's fields, and the text that follows them, out of the
/// node's tail.
extension RawSyntaxData.SmolParsedToken {
  /// - Parameter base: where this token's text begins, a fixed offset from the
  ///   node that holds these fields.
  func wholeText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(baseAddress: base, count: Int(self.wholeTextLength))
  }
  func tokenText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[self.textRange])
  }
  func leadingTriviaText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[..<self.textRange.lowerBound])
  }
  func trailingTriviaText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[self.textRange.upperBound...])
  }
}

extension RawSyntaxData.ParsedToken {
  /// - Parameter base: where this token's text begins, a fixed offset from the
  ///   node that holds these fields.
  func wholeText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(baseAddress: base, count: Int(self.wholeTextLength))
  }
  func tokenText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[self.textRange])
  }
  func leadingTriviaText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[..<self.textRange.lowerBound])
  }
  func trailingTriviaText(base: UnsafePointer<UInt8>) -> SyntaxText {
    SyntaxText(rebasing: self.wholeText(base: base)[self.textRange.upperBound...])
  }
}

extension RawSyntaxData.MaterializedToken {
  var leadingTrivia: RawTriviaPieceBuffer {
    RawTriviaPieceBuffer(rebasing: triviaPieces[..<Int(numLeadingTrivia)])
  }
  var trailingTrivia: RawTriviaPieceBuffer {
    RawTriviaPieceBuffer(rebasing: triviaPieces[Int(numLeadingTrivia)...])
  }
}

/// Represents the raw tree structure underlying the syntax tree. These nodes
/// have no notion of identity and only provide structure to the tree. They
/// are immutable and can be freely shared between syntax nodes.
@_spi(RawSyntax)
public struct RawSyntax: Sendable {

  /// Pointer to the node's header, which resides in a RawSyntaxArena and is
  /// followed by the node's tail.
  var pointer: ArenaAllocatedPointer<RawSyntaxData>
  init(pointer: ArenaAllocatedPointer<RawSyntaxData>) {
    self.pointer = pointer
  }

  /// Where a node's tail begins: immediately past its one-word header.
  @inline(__always)
  static var tailOffset: Int { MemoryLayout<RawSyntaxData>.stride }

  /// Where a layout node's children begin: past the header and the metadata.
  @inline(__always)
  static var childrenOffset: Int {
    Self.tailOffset + MemoryLayout<RawSyntaxData.Layout>.stride
  }

  @inline(__always)
  private var tail: UnsafeRawPointer {
    UnsafeRawPointer(pointer.pointer).advanced(by: Self.tailOffset)
  }

  @inline(__always)
  private static func allocate(
    _ header: RawSyntaxData,
    tailByteCount: Int,
    arena: __shared RawSyntaxArena
  ) -> (node: RawSyntax, tail: UnsafeMutableRawPointer) {
    let base = arena.allocateNode(byteCount: Self.tailOffset + tailByteCount)
    let headerPointer = base.assumingMemoryBound(to: RawSyntaxData.self)
    headerPointer.initialize(to: header)
    return (
      RawSyntax(pointer: ArenaAllocatedPointer(UnsafePointer(headerPointer))),
      base.advanced(by: Self.tailOffset)
    )
  }

  /// The token's text is copied into the node's tail, so the tree holds no
  /// reference to the buffer it was lexed from.
  /// The room a token's text needs in a node's tail: enough for `copyText` to
  /// write whole units without spilling past what was allocated.
  ///
  /// Four-byte units for short texts, which most punctuation and operators are:
  /// a three-byte token then wastes one byte rather than five. Identifiers and
  /// keywords are longer and keep the eight-byte units.
  ///
  /// - Important: `copyText` writes exactly this much, so the two must agree.
  @inline(__always)
  static func textByteCount(for count: Int) -> Int {
    count <= 4 ? (count + 3) & ~3 : (count + 7) & ~7
  }

  /// Copies `wholeText` into a node's tail, which must have
  /// `textByteCount(for:)` bytes of room.
  ///
  /// A short token is one load and one store this way, where `memcpy` spends
  /// longer choosing how to copy than it does copying. Reading the last unit
  /// runs past the token's end, so that form is taken only where those bytes are
  /// still inside the buffer being lexed.
  @inline(__always)
  private static func copyText(
    _ wholeText: SyntaxText,
    to destination: UnsafeMutableRawPointer,
    sourceBufferEnd: UnsafePointer<UInt8>?
  ) {
    guard let source = wholeText.baseAddress, !wholeText.isEmpty else { return }
    let count = wholeText.count
    guard let sourceBufferEnd,
      source + Self.textByteCount(for: count) <= sourceBufferEnd
    else {
      destination.copyMemory(from: source, byteCount: count)
      return
    }
    if count <= 4 {
      destination.storeBytes(
        of: UnsafeRawPointer(source).loadUnaligned(as: UInt32.self),
        as: UInt32.self
      )
    } else {
      var written = 0
      while written < count {
        destination.advanced(by: written).storeBytes(
          of: UnsafeRawPointer(source + written).loadUnaligned(as: UInt64.self),
          as: UInt64.self
        )
        written += 8
      }
    }
  }

  /// A token that is present, carries no diagnostic, and whose text is short
  /// enough to measure in a byte, which is almost every token in a file.
  init(
    arena: __shared RawSyntaxArena,
    smolParsedToken token: RawSyntaxData.SmolParsedToken,
    wholeText: SyntaxText,
    sourceBufferEnd: UnsafePointer<UInt8>?
  ) {
    let fieldsSize = MemoryLayout<RawSyntaxData.SmolParsedToken>.stride
    let (node, tail) = Self.allocate(
      .smolParsedToken(RawSyntaxArenaRef(arena)),
      tailByteCount: fieldsSize + Self.textByteCount(for: wholeText.count),
      arena: arena
    )
    tail.assumingMemoryBound(to: RawSyntaxData.SmolParsedToken.self).initialize(to: token)
    Self.copyText(wholeText, to: tail.advanced(by: fieldsSize), sourceBufferEnd: sourceBufferEnd)
    self = node
  }

  init(
    arena: __shared RawSyntaxArena,
    parsedToken token: RawSyntaxData.ParsedToken,
    wholeText: SyntaxText,
    sourceBufferEnd: UnsafePointer<UInt8>? = nil
  ) {
    // The text is rounded up to a word: it is the last thing in the node, the
    // next node is word aligned anyway, and it lets the copy write whole words.
    let fieldsSize = MemoryLayout<RawSyntaxData.ParsedToken>.stride
    let (node, tail) = Self.allocate(
      .parsedToken(RawSyntaxArenaRef(arena)),
      tailByteCount: fieldsSize + Self.textByteCount(for: wholeText.count),
      arena: arena
    )
    tail.assumingMemoryBound(to: RawSyntaxData.ParsedToken.self).initialize(to: token)
    Self.copyText(wholeText, to: tail.advanced(by: fieldsSize), sourceBufferEnd: sourceBufferEnd)
    self = node
  }

  init(arena: __shared RawSyntaxArena, materializedToken token: RawSyntaxData.MaterializedToken) {
    let (node, tail) = Self.allocate(
      .materializedToken(RawSyntaxArenaRef(arena)),
      tailByteCount: MemoryLayout<RawSyntaxData.MaterializedToken>.stride,
      arena: arena
    )
    tail.assumingMemoryBound(to: RawSyntaxData.MaterializedToken.self).initialize(to: token)
    self = node
  }

  /// Copies `children` into the node's tail.
  ///
  /// `makeLayout` builds its children in place instead; this is for the nodes
  /// made by replacing a child or trivia in an existing one.
  init(
    arena: __shared RawSyntaxArena,
    layoutKind kind: SyntaxKind,
    children: RawSyntaxBuffer,
    byteLength: UInt32,
    descendantCount: UInt32,
    recursiveFlags: RecursiveRawSyntaxFlags
  ) {
    let (node, tail) = Self.allocate(
      .layout(RawSyntaxArenaRef(arena)),
      tailByteCount: MemoryLayout<RawSyntaxData.Layout>.stride
        + children.count * MemoryLayout<RawSyntax?>.stride,
      arena: arena
    )
    tail.assumingMemoryBound(to: RawSyntaxData.Layout.self).initialize(
      to: RawSyntaxData.Layout(
        childCount: UInt32(children.count),
        byteLength: byteLength,
        descendantCount: descendantCount,
        kind: kind,
        recursiveFlags: recursiveFlags
      )
    )
    let destination = tail.advanced(by: MemoryLayout<RawSyntaxData.Layout>.stride)
      .assumingMemoryBound(to: RawSyntax?.self)
    for (offset, child) in children.enumerated() {
      destination.advanced(by: offset).initialize(to: child)
    }
    self = node
  }

  /// Which of the four shapes this node has, and the arena that owns it.
  @inline(__always)
  var header: RawSyntaxData {
    pointer.pointer.pointee
  }

  /// - Precondition: this is a short parsed token.
  @inline(__always)
  var smolParsedToken: UnsafePointer<RawSyntaxData.SmolParsedToken> {
    switch self.header {
    case .smolParsedToken:
      return tail.assumingMemoryBound(to: RawSyntaxData.SmolParsedToken.self)
    case .parsedToken, .materializedToken, .collection, .layout, .layoutWithUnexpected:
      preconditionFailure("not a short parsed token")
    }
  }

  /// - Precondition: this is a parsed token.
  @inline(__always)
  var parsedToken: UnsafePointer<RawSyntaxData.ParsedToken> {
    switch self.header {
    case .parsedToken:
      return tail.assumingMemoryBound(to: RawSyntaxData.ParsedToken.self)
    case .smolParsedToken, .materializedToken, .collection, .layout, .layoutWithUnexpected:
      preconditionFailure("not a parsed token")
    }
  }

  /// - Precondition: this is a materialized token.
  @inline(__always)
  var materializedToken: UnsafePointer<RawSyntaxData.MaterializedToken> {
    switch self.header {
    case .materializedToken:
      return tail.assumingMemoryBound(to: RawSyntaxData.MaterializedToken.self)
    case .smolParsedToken, .parsedToken, .collection, .layout, .layoutWithUnexpected:
      preconditionFailure("not a materialized token")
    }
  }

  /// - Precondition: this is a layout node or a collection.
  @inline(__always)
  var layout: UnsafePointer<RawSyntaxData.Layout> {
    switch self.header {
    case .collection, .layout, .layoutWithUnexpected:
      return tail.assumingMemoryBound(to: RawSyntaxData.Layout.self)
    case .smolParsedToken, .parsedToken, .materializedToken:
      preconditionFailure("not a layout node")
    }
  }

  /// Where a short parsed token's text begins.
  @inline(__always)
  var smolParsedTokenTextBase: UnsafePointer<UInt8> {
    tail.advanced(by: MemoryLayout<RawSyntaxData.SmolParsedToken>.stride)
      .assumingMemoryBound(to: UInt8.self)
  }

  /// Where a parsed token's text begins.
  @inline(__always)
  var parsedTokenTextBase: UnsafePointer<UInt8> {
    tail.advanced(by: MemoryLayout<RawSyntaxData.ParsedToken>.stride)
      .assumingMemoryBound(to: UInt8.self)
  }

  /// The node's children, which are tail allocated after its metadata.
  ///
  /// - Precondition: this is a layout node.
  @inline(__always)
  /// The slots this node holds: its real children, followed by its `unexpected`
  /// slots if it kept room for them.
  var physicalSlots: UnsafeBufferPointer<RawSyntax?> {
    let childCount = Int(tail.assumingMemoryBound(to: RawSyntaxData.Layout.self).pointee.childCount)
    let slotCount: Int
    switch self.header {
    case .layoutWithUnexpected:
      slotCount = 2 * childCount + 1
    case .collection, .layout:
      slotCount = childCount
    case .smolParsedToken, .parsedToken, .materializedToken:
      preconditionFailure("not a layout node")
    }
    let start = UnsafeRawPointer(pointer.pointer).advanced(by: Self.childrenOffset)
      .assumingMemoryBound(to: RawSyntax?.self)
    return UnsafeBufferPointer(start: start, count: slotCount)
  }

  /// This node's children as the tree describes them, which for a node that kept
  /// no room for its `unexpected` slots means reading those as nil.
  var logicalChildren: RawLayoutChildren {
    let childCount = Int(tail.assumingMemoryBound(to: RawSyntaxData.Layout.self).pointee.childCount)
    let start = UnsafeRawPointer(pointer.pointer).advanced(by: Self.childrenOffset)
      .assumingMemoryBound(to: RawSyntax?.self)
    let unexpected: UnsafeBufferPointer<RawSyntax?>
    switch self.header {
    case .layoutWithUnexpected:
      unexpected = UnsafeBufferPointer(start: start + childCount, count: childCount + 1)
    case .collection, .layout:
      unexpected = UnsafeBufferPointer(start: nil, count: 0)
    case .smolParsedToken, .parsedToken, .materializedToken:
      preconditionFailure("not a layout node")
    }
    return RawLayoutChildren(
      real: UnsafeBufferPointer(start: start, count: childCount),
      unexpected: unexpected,
      interleaves: self.kind.interleavesUnexpectedChildren
    )
  }

  public var arena: RetainedRawSyntaxArena {
    arenaReference.retained
  }

  internal var arenaReference: RawSyntaxArenaRef {
    pointer.pointer.pointee.arenaReference
  }

}

// MARK: - Accessors

extension RawSyntax {
  /// The syntax kind of this raw syntax.
  @_spi(RawSyntax)
  public var kind: SyntaxKind {
    switch self.header {
    case .smolParsedToken, .parsedToken, .materializedToken: return .token
    case .collection, .layout, .layoutWithUnexpected: return self.layout.pointee.kind
    }
  }

  /// Whether or not this node is a token one.
  @_spi(RawSyntax)
  public var isToken: Bool {
    kind == .token
  }

  var recursiveFlags: RecursiveRawSyntaxFlags {
    switch view {
    case .token(let tokenView):
      var recursiveFlags: RecursiveRawSyntaxFlags = []
      if tokenView.presence == .missing {
        recursiveFlags.insert(.hasError)
      }
      switch tokenView.tokenDiagnostic?.severity {
      case .error:
        recursiveFlags.insert(.hasError)
      case .warning:
        recursiveFlags.insert(.hasWarning)
      case nil:
        break
      }
      return recursiveFlags
    case .layout(let layoutView):
      return layoutView.recursiveFlags
    }
  }

  /// ``totalNodes`` and ``byteLength`` as they are stored, for
  /// ``makeLayout(kind:uninitializedCount:isMaximumNestingLevelOverflow:arena:initializingWith:)``,
  /// which sums both over every child of every node it builds — 300,000 times in
  /// parsing the performance test's declaration-heavy input. Going through the
  /// `Int` forms converts on each one.
  var totalNodes32: UInt32 {
    switch self.header {
    case .smolParsedToken, .parsedToken, .materializedToken:
      return 1
    case .collection, .layout, .layoutWithUnexpected:
      return self.layout.pointee.descendantCount + 1
    }
  }

  var byteLength32: UInt32 {
    switch self.header {
    case .smolParsedToken:
      // Present by construction, so nothing to test.
      return UInt32(self.smolParsedToken.pointee.wholeTextLength)
    case .parsedToken:
      let fields = self.parsedToken.pointee
      return fields.presence == .present ? fields.wholeTextLength : 0
    case .materializedToken:
      return self.materializedToken.pointee.presence == .present ? self.materializedToken.pointee.byteLength : 0
    case .collection, .layout, .layoutWithUnexpected:
      return self.layout.pointee.byteLength
    }
  }

  /// Total number of nodes in this sub-tree, including `self` node.
  var totalNodes: Int {
    switch self.header {
    case .smolParsedToken, .parsedToken, .materializedToken:
      return 1
    case .collection, .layout, .layoutWithUnexpected:
      return Int(self.layout.pointee.descendantCount) + 1
    }
  }

  /// The "width" of the node.
  ///
  /// Sum of text byte lengths of all present descendant token nodes.
  @_spi(RawSyntax)
  public var byteLength: Int {
    switch self.header {
    case .smolParsedToken:
      // Present by construction, so nothing to test.
      return Int(self.smolParsedToken.pointee.wholeTextLength)
    case .parsedToken:
      let fields = self.parsedToken.pointee
      if fields.presence == .present {
        return Int(fields.wholeTextLength)
      } else {
        return 0
      }
    case .materializedToken:
      if self.materializedToken.pointee.presence == .present {
        return Int(self.materializedToken.pointee.byteLength)
      } else {
        return 0
      }
    case .collection, .layout, .layoutWithUnexpected:
      return Int(self.layout.pointee.byteLength)
    }
  }

  var totalLength: SourceLength {
    SourceLength(utf8Length: byteLength)
  }

  /// Replaces the leading trivia of the first token in this syntax tree by `leadingTrivia`.
  /// If the syntax tree did not contain a token and thus no trivia could be attached to it, `nil` is returned.
  /// - Parameters:
  ///   - leadingTrivia: The trivia to attach.
  ///   - arena: RawSyntaxArena to the result node data resides.
  @_spi(RawSyntax)
  public func withLeadingTrivia(_ leadingTrivia: Trivia, arena: RawSyntaxArena) -> RawSyntax? {
    switch view {
    case .token(let tokenView):
      return .makeMaterializedToken(
        kind: tokenView.formKind(),
        leadingTrivia: leadingTrivia,
        trailingTrivia: tokenView.formTrailingTrivia(),
        presence: tokenView.presence,
        tokenDiagnostic: tokenView.tokenDiagnostic,
        arena: arena
      )
    case .layout(let layoutView):
      for (index, child) in layoutView.children.enumerated() {
        if let replaced = child?.withLeadingTrivia(leadingTrivia, arena: arena) {
          return layoutView.replacingChild(at: index, with: replaced, arena: arena)
        }
      }
      return nil
    }
  }

  /// Replaces the trailing trivia of the last token in this syntax tree by `trailingTrivia`.
  /// If the syntax tree did not contain a token and thus no trivia could be attached to it, `nil` is returned.
  /// - Parameters:
  ///   - trailingTrivia: The trivia to attach.
  ///   - arena: RawSyntaxArena to the result node data resides.
  @_spi(RawSyntax)
  public func withTrailingTrivia(_ trailingTrivia: Trivia, arena: RawSyntaxArena) -> RawSyntax? {
    switch view {
    case .token(let tokenView):
      return .makeMaterializedToken(
        kind: tokenView.formKind(),
        leadingTrivia: tokenView.formLeadingTrivia(),
        trailingTrivia: trailingTrivia,
        presence: tokenView.presence,
        tokenDiagnostic: tokenView.tokenDiagnostic,
        arena: arena
      )
    case .layout(let layoutView):
      for (index, child) in layoutView.children.enumerated().reversed() {
        if let replaced = child?.withTrailingTrivia(trailingTrivia, arena: arena) {
          return layoutView.replacingChild(at: index, with: replaced, arena: arena)
        }
      }
      return nil
    }
  }
}

extension RawTriviaPiece {
  /// Call `body` with the syntax text of this trivia piece.
  ///
  /// If `isEphemeral` is `true`, the ``SyntaxText`` argument is only guaranteed
  /// to be valid within the call.
  func withSyntaxText(body: (SyntaxText, _ isEphemeral: Bool) throws -> Void) rethrows {
    if let syntaxText = storedText {
      try body(syntaxText, /*isEphemeral*/ false)
      return
    }

    var description = ""
    write(to: &description)
    try description.withUTF8 { buffer in
      try body(
        SyntaxText(baseAddress: buffer.baseAddress, count: buffer.count),
        /*isEphemeral*/ true
      )
    }
  }
}

extension RawSyntax {
  /// Enumerate all of the syntax text present in this node, and all
  /// of its children, to give a source-accurate view of the bytes.
  ///
  /// Unlike `description`, this provides a source-accurate representation
  /// even in the presence of malformed UTF-8 in the input source.
  ///
  /// If `isEphemeral` is `true`, the ``SyntaxText`` arguments passed to the
  /// visitor are only guaranteed to be valid within that call. Otherwise, they
  /// are valid as long as the raw syntax is alive.
  public func withEachSyntaxText(body: (SyntaxText, _ isEphemeral: Bool) throws -> Void) rethrows {
    switch self.header {
    case .smolParsedToken:
      // Present by construction.
      try body(self.smolParsedToken.pointee.wholeText(base: self.smolParsedTokenTextBase), /*isEphemeral*/ false)
    case .parsedToken:
      if self.parsedToken.pointee.presence == .present {
        try body(self.parsedToken.pointee.wholeText(base: self.parsedTokenTextBase), /*isEphemeral*/ false)
      }
    case .materializedToken:
      if self.materializedToken.pointee.presence == .present {
        for p in self.materializedToken.pointee.leadingTrivia {
          try p.withSyntaxText(body: body)
        }
        try body(self.materializedToken.pointee.tokenText, /*isEphemeral*/ false)
        for p in self.materializedToken.pointee.trailingTrivia {
          try p.withSyntaxText(body: body)
        }
      }
    case .collection, .layout, .layoutWithUnexpected:
      for case let child? in self.logicalChildren {
        try child.withEachSyntaxText(body: body)
      }
    }
  }

  /// Retrieve the syntax text as an array of bytes that models the input
  /// source even in the presence of invalid UTF-8.
  public var syntaxTextBytes: [UInt8] {
    var result: [UInt8] = []
    var buf: SyntaxText = ""
    withEachSyntaxText { syntaxText, isEphemeral in
      if isEphemeral {
        result.append(contentsOf: buf)
        result.append(contentsOf: syntaxText)
        buf = ""
      } else if let base = buf.baseAddress, base + buf.count == syntaxText.baseAddress {
        buf = SyntaxText(baseAddress: base, count: buf.count + syntaxText.count)
      } else {
        result.append(contentsOf: buf)
        buf = syntaxText
      }
    }
    result.append(contentsOf: buf)
    return result
  }
}

extension RawSyntax: TextOutputStreamable, CustomStringConvertible {
  /// Prints the RawSyntax node, and all of its children, to the provided
  /// stream. This implementation must be source-accurate.
  /// - Parameter stream: The stream on which to output this node.
  public func write<Target: TextOutputStream>(to target: inout Target) {
    switch self.header {
    case .smolParsedToken:
      // Present by construction.
      String(syntaxText: self.smolParsedToken.pointee.wholeText(base: self.smolParsedTokenTextBase)).write(to: &target)
    case .parsedToken:
      if self.parsedToken.pointee.presence == .present {
        String(syntaxText: self.parsedToken.pointee.wholeText(base: self.parsedTokenTextBase)).write(to: &target)
      }
    case .materializedToken:
      if self.materializedToken.pointee.presence == .present {
        for p in self.materializedToken.pointee.leadingTrivia { p.write(to: &target) }
        String(syntaxText: self.materializedToken.pointee.tokenText).write(to: &target)
        for p in self.materializedToken.pointee.trailingTrivia { p.write(to: &target) }
      }
    case .collection, .layout, .layoutWithUnexpected:
      for case let child? in self.logicalChildren {
        child.write(to: &target)
      }
    }
  }

  /// A source-accurate description of this node.
  public var description: String {
    var s = ""
    self.write(to: &s)
    return s
  }
}

extension RawSyntax {
  /// Return the first token of a layout node that should be traversed by `viewMode`.
  func firstToken(viewMode: SyntaxTreeViewMode) -> RawSyntaxTokenView? {
    guard viewMode.shouldTraverse(node: self) else { return nil }
    switch view {
    case .token(let tokenView):
      return tokenView
    case .layout(let layoutView):
      for child in layoutView.children {
        if let token = child?.firstToken(viewMode: viewMode) {
          return token
        }
      }
      return nil
    }
  }

  /// Return the last token of a layout node that should be traversed by `viewMode`.
  func lastToken(viewMode: SyntaxTreeViewMode) -> RawSyntaxTokenView? {
    guard viewMode.shouldTraverse(node: self) else { return nil }
    switch view {
    case .token(let tokenView):
      return tokenView
    case .layout(let layoutView):
      for child in layoutView.children.reversed() {
        if let token = child?.lastToken(viewMode: viewMode) {
          return token
        }
      }
      return nil
    }
  }

  func formLeadingTrivia() -> Trivia {
    firstToken(viewMode: .sourceAccurate)?.formLeadingTrivia() ?? []
  }

  func formTrailingTrivia() -> Trivia {
    lastToken(viewMode: .sourceAccurate)?.formTrailingTrivia() ?? []
  }
}

extension RawSyntax {
  @_spi(RawSyntax)
  public var leadingTriviaByteLength: Int {
    firstToken(viewMode: .sourceAccurate)?.leadingTriviaByteLength ?? 0
  }

  @_spi(RawSyntax)
  public var trailingTriviaByteLength: Int {
    lastToken(viewMode: .sourceAccurate)?.trailingTriviaByteLength ?? 0
  }

  @_spi(RawSyntax)
  public var leadingTriviaPieces: [RawTriviaPiece]? {
    firstToken(viewMode: .sourceAccurate)?.leadingRawTriviaPieces
  }

  @_spi(RawSyntax)
  public var trailingTriviaPieces: [RawTriviaPiece]? {
    lastToken(viewMode: .sourceAccurate)?.trailingRawTriviaPieces
  }

  /// The length of this node’s content, without the first leading and the last
  /// trailing trivia. Intermediate trivia inside a layout node is included in
  /// this.
  var trimmedByteLength: Int {
    let result = byteLength - leadingTriviaByteLength - trailingTriviaByteLength
    precondition(result >= 0)
    return result
  }

  var leadingTriviaLength: SourceLength {
    SourceLength(utf8Length: leadingTriviaByteLength)
  }

  var trailingTriviaLength: SourceLength {
    SourceLength(utf8Length: trailingTriviaByteLength)
  }

  /// The length of this node excluding its leading and trailing trivia.
  var trimmedLength: SourceLength {
    SourceLength(utf8Length: trimmedByteLength)
  }
}

// MARK: - Factories.

extension RawSyntax {
  /// "Designated" factory method to create a parsed token node.
  ///
  /// - Parameters:
  ///   - kind: Token kind.
  ///   - wholeText: Whole text of this token including trailing/leading trivia.
  ///   - textRange: Range of the token text in `wholeText`.
  ///   - presence: Whether the token appeared in the source code or if it was synthesized.
  ///   - arena: RawSyntaxArena to the result node data resides.
  internal static func parsedToken(
    kind: RawTokenKind,
    wholeText: SyntaxText,
    textRange: Range<SyntaxText.Index>,
    presence: SourcePresence,
    tokenDiagnostic: TokenDiagnostic?,
    arena: __shared ParsingRawSyntaxArena
  ) -> RawSyntax {
    // The text is copied into the node itself, so the tree does not depend on
    // the buffer it was lexed from. `textRange` is 0-based within `wholeText`,
    // so it is unaffected by the copy.
    // Four bytes of fields rather than twenty, where the kind of node can imply
    // the presence and the absent diagnostic and a byte can hold the lengths.
    if presence == .present, tokenDiagnostic == nil,
      wholeText.count <= RawSyntaxData.SmolParsedToken.maximumTextLength
    {
      precondition(
        kind != .keyword || Keyword(SyntaxText(rebasing: wholeText[textRange])) != nil,
        "If kind is keyword, the text must be a known token kind"
      )
      return RawSyntax(
        arena: arena,
        smolParsedToken: RawSyntaxData.SmolParsedToken(
          wholeTextLength: UInt8(wholeText.count),
          textLowerBound: UInt8(textRange.lowerBound),
          textUpperBound: UInt8(textRange.upperBound),
          tokenKind: kind
        ),
        wholeText: wholeText,
        sourceBufferEnd: arena.sourceBufferEnd
      )
    }

    let payload = RawSyntaxData.ParsedToken(
      tokenKind: kind,
      wholeTextLength: wholeText.count,
      textRange: textRange,
      presence: presence,
      tokenDiagnostic: tokenDiagnostic
    )
    precondition(
      kind != .keyword || Keyword(SyntaxText(rebasing: wholeText[textRange])) != nil,
      "If kind is keyword, the text must be a known token kind"
    )
    return RawSyntax(
      arena: arena,
      parsedToken: payload,
      wholeText: wholeText,
      sourceBufferEnd: arena.sourceBufferEnd
    )
  }

  /// "Designated" factory method to create a materialized token node.
  ///
  /// This should not be called directly.
  /// Use `makeMaterializedToken(arena:kind:leadingTrivia:trailingTrivia:)` or
  /// `makeMissingToken(arena:kind:)` instead.
  ///
  /// - Parameters:
  ///   - kind: Token kind.
  ///   - text: Token text.
  ///   - triviaPieces: Raw trivia pieces including leading and trailing trivia.
  ///   - numLeadingTrivia: Number of leading trivia pieces in `triviaPieces`.
  ///   - byteLength: Byte length of this token including trivia.
  ///   - presence: Whether the token appeared in the source code or if it was synthesized.
  ///   - arena: RawSyntaxArena to the result node data resides.
  internal static func materializedToken(
    kind: RawTokenKind,
    text: SyntaxText,
    triviaPieces: RawTriviaPieceBuffer,
    numLeadingTrivia: UInt32,
    byteLength: UInt32,
    presence: SourcePresence,
    tokenDiagnostic: TokenDiagnostic?,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    // A materialized token's `text` must outlive the tree. Callers may pass text
    // that is already arena-managed, a static default (`kind.defaultText`), or -
    // during parsing - a slice of the `Parser`-owned source buffer, which does
    // *not* outlive the parse. Intern dynamic text so the token is always
    // self-contained. `intern` is a no-op for already-arena-managed (and empty)
    // text, and we skip static defaults to avoid copying constants into every
    // token.
    let text = kind.defaultText?.baseAddress == text.baseAddress ? text : arena.intern(text)
    let payload = RawSyntaxData.MaterializedToken(
      tokenKind: kind,
      tokenText: text,
      triviaPieces: triviaPieces,
      numLeadingTrivia: numLeadingTrivia,
      byteLength: byteLength,
      presence: presence,
      tokenDiagnostic: tokenDiagnostic
    )
    precondition(kind != .keyword || Keyword(text) != nil, "If kind is keyword, the text must be a known token kind")
    return RawSyntax(arena: arena, materializedToken: payload)
  }

  /// Factory method to create a materialized token node.
  ///
  /// - Parameters:
  ///   - kind: Token kind.
  ///   - text: Token text.
  ///   - leadingTriviaPieceCount: Number of leading trivia pieces.
  ///   - trailingTriviaPieceCount: Number of trailing trivia pieces.
  ///   - presence: Whether the token appeared in the source code or if it was synthesized.
  ///   - arena: RawSyntaxArena to the result node data resides.
  ///   - initializingLeadingTriviaWith: A closure that initializes leading trivia pieces.
  ///   - initializingTrailingTriviaWith: A closure that initializes trailing trivia pieces.
  public static func makeMaterializedToken(
    kind: RawTokenKind,
    text: SyntaxText,
    leadingTriviaPieceCount: Int,
    trailingTriviaPieceCount: Int,
    presence: SourcePresence,
    tokenDiagnostic: TokenDiagnostic?,
    arena: __shared RawSyntaxArena,
    initializingLeadingTriviaWith: (UnsafeMutableBufferPointer<RawTriviaPiece>) -> Void,
    initializingTrailingTriviaWith: (UnsafeMutableBufferPointer<RawTriviaPiece>) -> Void
  ) -> RawSyntax {
    precondition(kind.defaultText == nil || text.isEmpty || kind.defaultText == text)
    let totalTriviaCount = leadingTriviaPieceCount + trailingTriviaPieceCount
    let triviaBuffer = arena.allocateRawTriviaPieceBuffer(count: totalTriviaCount)
    initializingLeadingTriviaWith(
      UnsafeMutableBufferPointer(rebasing: triviaBuffer[..<leadingTriviaPieceCount])
    )
    initializingTrailingTriviaWith(
      UnsafeMutableBufferPointer(rebasing: triviaBuffer[leadingTriviaPieceCount...])
    )

    let byteLength = text.count + triviaBuffer.reduce(0, { $0 + $1.byteLength })
    return .materializedToken(
      kind: kind,
      text: text,
      triviaPieces: RawTriviaPieceBuffer(UnsafeBufferPointer(triviaBuffer)),
      numLeadingTrivia: numericCast(leadingTriviaPieceCount),
      byteLength: numericCast(byteLength),
      presence: presence,
      tokenDiagnostic: tokenDiagnostic,
      arena: arena
    )
  }

  /// Factory method to create a materialized token node.
  ///
  /// - Parameters:
  ///   - arena: RawSyntaxArena to the result node data resides.
  ///   - kind: Token kind.
  ///   - text: Token text.
  ///   - leadingTrivia: Leading trivia.
  ///   - trailingTrivia: Trailing trivia.
  static func makeMaterializedToken(
    kind: TokenKind,
    leadingTrivia: Trivia,
    trailingTrivia: Trivia,
    presence: SourcePresence,
    tokenDiagnostic: TokenDiagnostic?,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    let decomposed = kind.decomposeToRaw()
    let rawKind = decomposed.rawKind
    let text = (decomposed.string.map({ arena.intern($0) }) ?? decomposed.rawKind.defaultText ?? "")

    return .makeMaterializedToken(
      kind: rawKind,
      text: text,
      leadingTriviaPieceCount: leadingTrivia.count,
      trailingTriviaPieceCount: trailingTrivia.count,
      presence: presence,
      tokenDiagnostic: tokenDiagnostic,
      arena: arena,
      initializingLeadingTriviaWith: { buffer in
        guard var ptr = buffer.baseAddress else { return }
        for piece in leadingTrivia {
          ptr.initialize(to: .make(piece, arena: arena))
          ptr += 1
        }
      },
      initializingTrailingTriviaWith: { buffer in
        guard var ptr = buffer.baseAddress else { return }
        for piece in trailingTrivia {
          ptr.initialize(to: .make(piece, arena: arena))
          ptr += 1
        }
      }
    )
  }

  static func makeMissingToken(
    kind: TokenKind,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    let (rawKind, _) = kind.decomposeToRaw()
    return .materializedToken(
      kind: rawKind,
      text: rawKind.defaultText ?? "",
      triviaPieces: RawTriviaPieceBuffer(),
      numLeadingTrivia: 0,
      byteLength: 0,
      presence: .missing,
      tokenDiagnostic: nil,
      arena: arena
    )
  }
}

extension RawSyntax {
  /// "Designated" factory method to create a layout node.
  ///
  /// This should not be called directly.
  /// Use `makeLayout(arena:kind:uninitializedCount:initializingWith:)` or
  /// `makeEmptyLayout(arena:kind:)` instead.
  ///
  /// - Parameters:
  ///   - arena: RawSyntaxArena to the result node data resides.
  ///   - kind: Syntax kind. This should not be `.token`.
  ///   - layout: Layout buffer of the children.
  ///   - byteLength: Computed total byte length of this node.
  ///   - descendantCount: Total number of the descendant nodes in `layout`.
  /// The counts as they are stored, for
  /// ``makeLayout(kind:uninitializedCount:isMaximumNestingLevelOverflow:arena:initializingWith:)``,
  /// which has summed them narrow.
  fileprivate static func layout(
    kind: SyntaxKind,
    layout: RawSyntaxBuffer,
    byteLength: UInt32,
    descendantCount: UInt32,
    recursiveFlags: RecursiveRawSyntaxFlags,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    validateLayout(layout: layout, as: kind)
    return RawSyntax(
      arena: arena,
      layoutKind: kind,
      children: layout,
      byteLength: byteLength,
      descendantCount: descendantCount,
      recursiveFlags: recursiveFlags
    )
  }

  fileprivate static func layout(
    kind: SyntaxKind,
    layout: RawSyntaxBuffer,
    byteLength: Int,
    descendantCount: Int,
    recursiveFlags: RecursiveRawSyntaxFlags,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    validateLayout(layout: layout, as: kind)
    return RawSyntax(
      arena: arena,
      layoutKind: kind,
      children: layout,
      byteLength: UInt32(byteLength),
      descendantCount: UInt32(descendantCount),
      recursiveFlags: recursiveFlags
    )
  }

  /// Factory method to create a layout node.
  ///
  /// - Parameters:
  ///   - arena: RawSyntaxArena to the result node data resides.
  ///   - kind: Syntax kind.
  ///   - count: Number of children.
  ///   - initializer: A closure that initializes elements.
  /// - Important: `@inline(__always)` because this is how every layout node in
  ///   a tree is built, and the generated initializers are its only callers.
  ///   Narrowing the fields of `Layout` grew this enough that the compiler
  ///   stopped inlining it, which cost 0.19 ms of a parse — more than the
  ///   narrowing saved anywhere else.
  @inline(__always)
  public static func makeLayout(
    kind: SyntaxKind,
    uninitializedCount count: Int,
    isMaximumNestingLevelOverflow: Bool = false,
    arena: __shared RawSyntaxArena,
    initializingWith initializer: (UnsafeMutableBufferPointer<RawSyntax?>) -> Void
  ) -> RawSyntax {
    // `initializer` writes the layout as the tree describes it, with an
    // `unexpected` slot before the first child, between each pair and after the
    // last. Whether any of those slots is occupied decides how much memory the
    // node needs, and it is not known until the initializer has run — so it runs
    // into a temporary first. A layout node has at most 23 slots.
    return withUnsafeTemporaryAllocation(of: RawSyntax?.self, capacity: count) { logical in
      initializer(logical)

      let interleaves = kind.interleavesUnexpectedChildren
      // Real children are the odd slots when a kind interleaves, and all of them
      // when it does not.
      let childCount = interleaves ? (count - 1) / 2 : count

      var hasUnexpected = false
      if interleaves {
        for i in stride(from: 0, to: count, by: 2) where logical[i] != nil {
          hasUnexpected = true
          break
        }
      }

      let arenaRef = RawSyntaxArenaRef(arena)
      let header: RawSyntaxData
      if kind.isSyntaxCollection {
        header = .collection(arenaRef)
      } else if hasUnexpected {
        header = .layoutWithUnexpected(arenaRef)
      } else {
        header = .layout(arenaRef)
      }
      // A node keeps room for its `unexpected` slots only when it has something
      // to put in them, which is what this whole shape is for.
      let slotCount = hasUnexpected ? count : childCount

      let (node, tail) = Self.allocate(
        header,
        tailByteCount: MemoryLayout<RawSyntaxData.Layout>.stride
          + slotCount * MemoryLayout<RawSyntax?>.stride,
        arena: arena
      )
      let slots = UnsafeMutableBufferPointer<RawSyntax?>(
        start: tail.advanced(by: MemoryLayout<RawSyntaxData.Layout>.stride)
          .assumingMemoryBound(to: RawSyntax?.self),
        count: slotCount
      )
      // Real children first, so that reaching one is the same constant index
      // whichever shape the node has.
      if interleaves {
        for k in 0..<childCount {
          slots.initializeElement(at: k, to: logical[2 * k + 1])
        }
        if hasUnexpected {
          for j in 0...childCount {
            slots.initializeElement(at: childCount + j, to: logical[2 * j])
          }
        }
      } else {
        for i in 0..<count {
          slots.initializeElement(at: i, to: logical[i])
        }
      }

      // Calculate the "byte width".
      var byteLength: UInt32 = 0
      var descendantCount: UInt32 = 0
      var recursiveFlags = RecursiveRawSyntaxFlags()
      if kind.hasError {
        recursiveFlags.insert(.hasError)
      }
      for case let child? in logical {
        byteLength += child.byteLength32
        descendantCount += child.totalNodes32
        recursiveFlags.insert(child.recursiveFlags)
        arena.addChild(child.arenaReference)
      }
      if kind == .sequenceExpr {
        recursiveFlags.insert(.hasSequenceExpr)
      }
      if isMaximumNestingLevelOverflow {
        recursiveFlags.insert(.hasMaximumNestingLevelOverflow)
      }

      tail.assumingMemoryBound(to: RawSyntaxData.Layout.self).initialize(
        to: RawSyntaxData.Layout(
          childCount: UInt32(childCount),
          byteLength: byteLength,
          descendantCount: descendantCount,
          kind: kind,
          recursiveFlags: recursiveFlags
        )
      )
      return node
    }
  }

  static func makeEmptyLayout(
    kind: SyntaxKind,
    arena: __shared RawSyntaxArena
  ) -> RawSyntax {
    var recursiveFlags = RecursiveRawSyntaxFlags()
    if kind.hasError {
      recursiveFlags.insert(.hasError)
    }
    return .layout(
      kind: kind,
      layout: RawSyntaxBuffer(),
      byteLength: 0,
      descendantCount: 0,
      recursiveFlags: recursiveFlags,
      arena: arena
    )
  }

  static func makeLayout(
    kind: SyntaxKind,
    from collection: some Collection<RawSyntax?>,
    arena: __shared RawSyntaxArena,
    leadingTrivia: Trivia? = nil,
    trailingTrivia: Trivia? = nil
  ) -> RawSyntax {
    if leadingTrivia != nil || trailingTrivia != nil {
      var layout = Array(collection)
      if let leadingTrivia = leadingTrivia,
        // Find the index of the first non-empty node so we can attach the trivia to it.
        let idx = layout.firstIndex(where: { $0 != nil && ($0!.isToken || $0!.totalNodes > 1) })
      {
        layout[idx] = layout[idx]!.withLeadingTrivia(
          leadingTrivia + (layout[idx]?.formLeadingTrivia() ?? []),
          arena: arena
        )
      }
      if let trailingTrivia = trailingTrivia,
        // Find the index of the first non-empty node so we can attach the trivia to it.
        let idx = layout.lastIndex(where: { $0 != nil && ($0!.isToken || $0!.totalNodes > 1) })
      {
        layout[idx] = layout[idx]!.withTrailingTrivia(
          (layout[idx]?.formTrailingTrivia() ?? []) + trailingTrivia,
          arena: arena
        )
      }
      return .makeLayout(kind: kind, from: layout, arena: arena)
    }

    return .makeLayout(kind: kind, uninitializedCount: collection.count, arena: arena) {
      _ = $0.initialize(from: collection)
    }
  }
}

// MARK: - Debugging.

extension RawSyntax: CustomDebugStringConvertible {

  private func debugWrite(to target: inout some TextOutputStream, indent: Int, withChildren: Bool = false) {
    let childIndent = indent + 2
    switch self.header {
    case .smolParsedToken:
      target.write(".parsedToken(")
      target.write(String(describing: self.smolParsedToken.pointee.tokenKind))
      target.write(
        " wholeText=\(self.smolParsedToken.pointee.wholeText(base: self.smolParsedTokenTextBase).debugDescription)"
      )
      target.write(" textRange=\(self.smolParsedToken.pointee.textRange.description)")
    case .parsedToken:
      target.write(".parsedToken(")
      target.write(String(describing: self.parsedToken.pointee.tokenKind))
      target.write(" wholeText=\(self.parsedToken.pointee.wholeText(base: self.parsedTokenTextBase).debugDescription)")
      target.write(" textRange=\(self.parsedToken.pointee.textRange.description)")
    case .materializedToken:
      target.write(".materializedToken(")
      target.write(String(describing: self.materializedToken.pointee.tokenKind))
      target.write(" text=\(self.materializedToken.pointee.tokenText.debugDescription)")
      target.write(" numLeadingTrivia=\(self.materializedToken.pointee.numLeadingTrivia)")
      target.write(" byteLength=\(self.materializedToken.pointee.byteLength)")
      break
    case .collection, .layout, .layoutWithUnexpected:
      target.write(".layout(")
      target.write(String(describing: kind))
      target.write(" byteLength=\(Int(self.layout.pointee.byteLength))")
      target.write(" descendantCount=\(Int(self.layout.pointee.descendantCount))")
      if withChildren {
        for (num, child) in self.logicalChildren.enumerated() {
          target.write("\n")
          target.write(String(repeating: " ", count: childIndent))
          target.write("\(num): ")
          if let child = child {
            child.debugWrite(to: &target, indent: childIndent)
          } else {
            target.write("<nil>")
          }
        }
      }
      break
    }
    target.write(")")
  }

  @_spi(RawSyntax)
  public var debugDescription: String {
    var string = ""
    debugWrite(to: &string, indent: 0, withChildren: false)
    return string
  }
}

extension RawSyntax: CustomReflectable {
  @_spi(RawSyntax)
  public var customMirror: Mirror {

    let mirrorChildren: [Any]
    switch view {
    case .token:
      mirrorChildren = []
    case .layout(let layoutView):
      mirrorChildren = layoutView.children.map {
        child in child ?? (nil as Any?) as Any
      }
    }
    return Mirror(self, unlabeledChildren: mirrorChildren)
  }
}

enum RawSyntaxView {
  case token(RawSyntaxTokenView)
  case layout(RawSyntaxLayoutView)
}

extension RawSyntax {
  var view: RawSyntaxView {
    switch raw.header {
    case .smolParsedToken, .parsedToken, .materializedToken:
      return .token(tokenView!)
    case .collection, .layout, .layoutWithUnexpected:
      return .layout(layoutView!)
    }
  }
}

extension RawSyntax: Identifiable {
  public struct ID: Hashable, @unchecked Sendable {
    /// The pointer to the start of the `RawSyntax` node.
    fileprivate var pointer: UnsafeRawPointer
    fileprivate init(_ raw: RawSyntax) {
      self.pointer = raw.pointer.unsafeRawPointer
    }
  }

  public var id: ID {
    return ID(self)
  }
}

/// See `SyntaxMemoryLayout`.
let RawSyntaxDataMemoryLayouts: [String: SyntaxMemoryLayout.Value] = [
  "RawSyntaxData": .init(RawSyntaxData.self),
  "RawSyntaxData.SmolParsedToken": .init(RawSyntaxData.SmolParsedToken.self),
  "RawSyntaxData.ParsedToken": .init(RawSyntaxData.ParsedToken.self),
  "RawSyntaxData.MaterializedToken": .init(RawSyntaxData.MaterializedToken.self),
  "RawSyntaxData.Layout": .init(RawSyntaxData.Layout.self),
  "RawSyntax?": .init(RawSyntax?.self),
]
