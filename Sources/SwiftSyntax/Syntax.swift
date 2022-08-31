//===--------------- Syntax.swift - Base Syntax Type eraser  --------------===//
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

/// A Syntax node represents a tree of nodes with tokens at the leaves.
/// Each node has accessors for its known children, and allows efficient
/// iteration over the children through its `children` property.
public struct Syntax: SyntaxProtocol, SyntaxHashable {
  let data: SyntaxData

  public var _syntaxNode: Syntax {
    return self
  }

  init(_ data: SyntaxData) {
    self.data = data
  }

  @_spi(RawSyntax)
  public init(raw: RawSyntax) {
    self.init(.forRoot(raw))
  }

  /// Create a `Syntax` node from a specialized syntax node.
  public init<S: SyntaxProtocol>(_ syntax: S) {
    self = syntax._syntaxNode
  }

  /// Create a `Syntax` node from a specialized optional syntax node.
  public init?<S: SyntaxProtocol>(_ syntax: S?) {
    guard let syntax = syntax else { return nil }
    self = syntax._syntaxNode
  }
  
  public init(fromProtocol syntax: SyntaxProtocol) {
    self = syntax._syntaxNode
  }
  
  public init?(fromProtocol syntax: SyntaxProtocol?) {
    guard let syntax = syntax else { return nil }
    self = syntax._syntaxNode
  }

  public func hash(into hasher: inout Hasher) {
    return data.nodeId.hash(into: &hasher)
  }

  public static func ==(lhs: Syntax, rhs: Syntax) -> Bool {
    return lhs.data.nodeId == rhs.data.nodeId
  }
}

// Casting functions to specialized syntax nodes.
extension Syntax {
  public func `is`<S: SyntaxProtocol>(_ syntaxType: S.Type) -> Bool {
    return self.as(syntaxType) != nil
  }

  public func `as`<S: SyntaxProtocol>(_ syntaxType: S.Type) -> S? {
    return S.init(self)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self.asProtocol(SyntaxProtocol.self))
  }
}

extension Syntax: CustomReflectable {
  /// Reconstructs the real syntax type for this type from the node's kind and
  /// provides a mirror that reflects this type.
  public var customMirror: Mirror {
    return Mirror(reflecting: self.asProtocol(SyntaxProtocol.self))
  }
}

extension Syntax: Identifiable {
  public typealias ID = SyntaxIdentifier
}

/// Protocol that provides a common Hashable implementation for all syntax nodes
public protocol SyntaxHashable: Hashable {
  var _syntaxNode: Syntax { get }
}

public extension SyntaxHashable {
  func hash(into hasher: inout Hasher) {
    return _syntaxNode.data.nodeId.hash(into: &hasher)
  }

  static func ==(lhs: Self, rhs: Self) -> Bool {
    return lhs._syntaxNode.data.nodeId == rhs._syntaxNode.data.nodeId
  }
}

/// Provide common functionality for specialized syntax nodes. Extend this
/// protocol to provide common functionality for all syntax nodes.
/// DO NOT CONFORM TO THIS PROTOCOL YOURSELF!
public protocol SyntaxProtocol: CustomStringConvertible,
    CustomDebugStringConvertible, TextOutputStreamable {

  /// Retrieve the generic syntax node that is represented by this node.
  /// Do not retrieve this property directly. Use `Syntax(self)` instead.
  var _syntaxNode: Syntax { get }

  /// Converts the given `Syntax` node to this type. Returns `nil` if the
  /// conversion is not possible.
  init?(_ syntaxNode: Syntax)

  /// Returns the underlying syntax node type.
  var syntaxNodeType: SyntaxProtocol.Type { get }
}

extension SyntaxProtocol {
  var data: SyntaxData {
    return _syntaxNode.data
  }

  /// Access the raw syntax assuming the node is a Syntax.
  @_spi(RawSyntax)
  public var raw: RawSyntax {
    return _syntaxNode.data.raw
  }
}

public extension SyntaxProtocol {
  @available(*, deprecated, message: "Use children(viewMode:) instead")
  var children: SyntaxChildren {
    return children(viewMode: .sourceAccurate)
  }

  /// A sequence over the `present` children of this node.
  func children(viewMode: SyntaxTreeViewMode) -> SyntaxChildren {
    return SyntaxChildren(_syntaxNode, viewMode: viewMode)
  }

  /// The index of this node in a `SyntaxChildren` collection.
  var index: SyntaxChildrenIndex {
    return SyntaxChildrenIndex(self.data.absoluteRaw.info)
  }

  /// Whether or not this node is a token one.
  var isToken: Bool {
    return raw.isToken
  }

  /// Whether or not this node represents an SyntaxCollection.
  var isCollection: Bool {
    // We need to provide a custom implementation for is(SyntaxCollection.self)
    // since SyntaxCollection has generic or self requirements and can thus
    // not be used as a method argument.
    return raw.kind.isSyntaxCollection
  }

  /// Whether or not this node represents an unknown node.
  var isUnknown: Bool {
    return raw.kind.isUnknown
  }

  /// Whether this tree contains a missing token or unexpected node.
  var hasError: Bool {
    return raw.recursiveFlags.contains(.hasError)
  }

  /// The parent of this syntax node, or `nil` if this node is the root.
  var parent: Syntax? {
    return data.parent
  }

  /// The index of this node in the parent's children.
  var indexInParent: Int {
    return data.indexInParent
  }

  /// Whether or not this node has a parent.
  var hasParent: Bool {
    return parent != nil
  }

  /// Recursively walks through the tree to find the token semantically before
  /// this node.
  var previousToken: TokenSyntax? {
    return self.previousToken(viewMode: .sourceAccurate)
  }

  /// Recursively walks through the tree to find the token semantically before
  /// this node.
  func previousToken(viewMode: SyntaxTreeViewMode) -> TokenSyntax? {
    guard let parent = self.parent else {
      return nil
    }
    let siblings = NonNilRawSyntaxChildren(parent, viewMode: viewMode)
    for absoluteRaw in siblings[..<self.index].reversed() {
      let child = Syntax(SyntaxData(absoluteRaw, parent: parent))
      if let token = child.lastToken(viewMode: viewMode) {
        return token
      }
    }
    return parent.previousToken(viewMode: viewMode)
  }

  /// Recursively walks through the tree to find the next token semantically
  /// after this node.
  var nextToken: TokenSyntax? {
    return self.nextToken(viewMode: .sourceAccurate)
  }

  /// Recursively walks through the tree to find the next token semantically
  /// after this node.
  func nextToken(viewMode: SyntaxTreeViewMode) -> TokenSyntax? {
    guard let parent = self.parent else {
      return nil
    }
    let siblings = NonNilRawSyntaxChildren(parent, viewMode: viewMode)
    let nextSiblingIndex = siblings.index(after: self.index)
    for absoluteRaw in siblings[nextSiblingIndex...] {
      let child = Syntax(SyntaxData(absoluteRaw, parent: parent))
      if let token = child.firstToken(viewMode: viewMode) {
        return token
      }
    }
    return parent.nextToken(viewMode: viewMode)
  }

  /// Returns the first token in this syntax node in the source accurate view of
  /// the syntax tree.
  var firstToken: TokenSyntax? {
    return self.firstToken(viewMode: .sourceAccurate)
  }

  /// Returns the first token node that is part of this syntax node.
  func firstToken(viewMode: SyntaxTreeViewMode) -> TokenSyntax? {
    guard viewMode.shouldTraverse(node: raw) else { return nil }
    if let token = _syntaxNode.as(TokenSyntax.self) {
      return token
    }

    for child in children(viewMode: viewMode) {
      if let token = child.firstToken(viewMode: viewMode) {
        return token
      }
    }
    return nil
  }

  /// Returns the last token node that is part of this syntax node.
  var lastToken: TokenSyntax? {
    return self.lastToken(viewMode: .sourceAccurate)
  }

  /// Returns the last token node that is part of this syntax node.
  func lastToken(viewMode: SyntaxTreeViewMode) -> TokenSyntax? {
    guard viewMode.shouldTraverse(node: raw) else { return nil }
    if let token = _syntaxNode.as(TokenSyntax.self) {
      return token
    }

    for child in children(viewMode: viewMode).reversed() {
      if let tok = child.lastToken(viewMode: viewMode) {
        return tok
      }
    }
    return nil
  }

  /// The absolute position of the starting point of this node. If the first token
  /// is with leading trivia, the position points to the start of the leading
  /// trivia.
  var position: AbsolutePosition {
    return data.position
  }

  /// The absolute position of the starting point of this node, skipping any
  /// leading trivia attached to the first token syntax.
  var positionAfterSkippingLeadingTrivia: AbsolutePosition {
    return data.positionAfterSkippingLeadingTrivia
  }

  /// The end position of this node's content, before any trailing trivia.
  var endPositionBeforeTrailingTrivia: AbsolutePosition {
    return data.endPositionBeforeTrailingTrivia
  }

  /// The end position of this node, including its trivia.
  var endPosition: AbsolutePosition {
    return data.endPosition
  }

  /// The textual byte length of this node including leading and trailing trivia.
  var byteSize: Int {
    return totalLength.utf8Length
  }

  /// The byte source range of this node including leading and trailing trivia.
  var byteRange: ByteSourceRange {
    return ByteSourceRange(offset: position.utf8Offset, length: byteSize)
  }

  /// The length this node takes up spelled out in the source, excluding its
  /// leading or trailing trivia.
  var contentLength: SourceLength {
    return raw.contentLength
  }

  /// The leading trivia of this syntax node. Leading trivia is attached to
  /// the first token syntax contained by this node. Without such token, this
  /// property will return nil.
  var leadingTrivia: Trivia? {
    get {
      return raw.formLeadingTrivia()
    }
    set {
      self = withLeadingTrivia(newValue ?? [])
    }
  }

  /// The trailing trivia of this syntax node. Trailing trivia is attached to
  /// the last token syntax contained by this node. Without such token, this
  /// property will return nil.
  var trailingTrivia: Trivia? {
    get {
      return raw.formTrailingTrivia()
    }
    set {
      self = withTrailingTrivia(newValue ?? [])
    }
  }

  /// The length this node's leading trivia takes up spelled out in source.
  var leadingTriviaLength: SourceLength {
    return raw.leadingTriviaLength
  }

  /// The length this node's trailing trivia takes up spelled out in source.
  var trailingTriviaLength: SourceLength {
    return raw.trailingTriviaLength
  }

  /// Returns a new syntax node with its leading trivia replaced
  /// by the provided trivia.
  func withLeadingTrivia(_ leadingTrivia: Trivia) -> Self {
    return Self(Syntax(data.withLeadingTrivia(leadingTrivia)))!
  }

  /// Returns a new syntax node with its trailing trivia replaced
  /// by the provided trivia.
  func withTrailingTrivia(_ trailingTrivia: Trivia) -> Self {
    return Self(Syntax(data.withTrailingTrivia(trailingTrivia)))!
  }

  /// Returns a new syntax node with its leading trivia removed.
  func withoutLeadingTrivia() -> Self {
    return withLeadingTrivia([])
  }

  /// Returns a new syntax node with its trailing trivia removed.
  func withoutTrailingTrivia() -> Self {
    return withTrailingTrivia([])
  }

  /// Returns a new syntax node with all trivia removed.
  func withoutTrivia() -> Self {
    return withoutLeadingTrivia().withoutTrailingTrivia()
  }

  /// The length of this node including all of its trivia.
  var totalLength: SourceLength {
    return raw.totalLength
  }

  /// When isImplicit is true, the syntax node doesn't include any
  /// underlying tokens, e.g. an empty CodeBlockItemList.
  var isImplicit: Bool {
    return leadingTrivia == nil
  }

  /// The textual byte length of this node exluding leading and trailing trivia.
  var byteSizeAfterTrimmingTrivia: Int {
    return contentLength.utf8Length
  }

  /// The root of the tree in which this node resides.
  var root: Syntax {
    var this = _syntaxNode
    while let parent = this.parent {
      this = parent
    }
    return this
  }

  /// Sequence of tokens that are part of this Syntax node.
  @available(*, deprecated, message: "Use tokens(viewMode:) instead")
  var tokens: TokenSequence {
    return tokens(viewMode: .sourceAccurate)
  }

  /// Sequence of tokens that are part of this Syntax node.
  func tokens(viewMode: SyntaxTreeViewMode) -> TokenSequence {
    return TokenSequence(_syntaxNode, viewMode: viewMode)
  }

  /// Sequence of `SyntaxClassifiedRange`s for this syntax node.
  ///
  /// The provided classified ranges are consecutive and cover the full source
  /// text of the node. The ranges may also span multiple tokens, if multiple
  /// consecutive tokens would have the same classification then a single classified
  /// range is provided for all of them.
  var classifications: SyntaxClassifications {
    let fullRange = ByteSourceRange(offset: 0, length: byteSize)
    return SyntaxClassifications(_syntaxNode, in: fullRange)
  }

  /// Sequence of `SyntaxClassifiedRange`s contained in this syntax node within
  /// a relative range.
  ///
  /// The provided classified ranges may extend beyond the provided `range`.
  /// Active classifications (non-`none`) will extend the range to include the
  /// full classified range (e.g. from the beginning of the comment block), while
  /// `none` classified ranges will extend to the beginning or end of the token
  /// that the `range` touches.
  /// It is guaranteed that no classified range will be provided that doesn't
  /// intersect the provided `range`.
  ///
  /// - Parameters:
  ///   - in: The relative byte range to pull `SyntaxClassifiedRange`s from.
  /// - Returns: Sequence of `SyntaxClassifiedRange`s.
  func classifications(in range: ByteSourceRange) -> SyntaxClassifications {
    return SyntaxClassifications(_syntaxNode, in: range)
  }

  /// The `SyntaxClassifiedRange` for a relative byte offset.
  /// - Parameters:
  ///   - at: The relative to the node byte offset.
  /// - Returns: The `SyntaxClassifiedRange` for the offset or nil if the source text
  ///   at the given offset is unclassified.
  func classification(at offset: Int) -> SyntaxClassifiedRange? {
    let classifications = SyntaxClassifications(_syntaxNode, in: ByteSourceRange(offset: offset, length: 1))
    var iterator = classifications.makeIterator()
    return iterator.next()
  }

  /// The `SyntaxClassifiedRange` for an absolute position.
  /// - Parameters:
  ///   - at: The absolute position.
  /// - Returns: The `SyntaxClassifiedRange` for the position or nil if the source text
  ///   at the given position is unclassified.
  func classification(at position: AbsolutePosition) -> SyntaxClassifiedRange? {
    let relativeOffset = position.utf8Offset - self.position.utf8Offset
    return self.classification(at: relativeOffset)
  }

  /// Returns a value representing the unique identity of the node.
  var id: SyntaxIdentifier {
    return data.nodeId
  }
}

/// Provides the source-accurate text for a node
public extension SyntaxProtocol {
  /// A source-accurate description of this node.
  var description: String {
    return data.raw.description
  }

  /// Prints the raw value of this node to the provided stream.
  /// - Parameter stream: The stream to which to print the raw tree.
  func write<Target>(to target: inout Target)
    where Target: TextOutputStream {
    data.raw.write(to: &target)
  }
}

/// Provides debug descriptions for a node
public extension SyntaxProtocol {
  /// A simple description of this node (ie. its type).
  var debugDescription: String {
    debugDescription()
  }

  /// Same as `debugDescription` but includes all children.
  var recursiveDescription: String {
    debugDescription(includeChildren: true)
  }

  /// Returns a summarized dump of this node.
  /// - Parameters:
  ///   - includeChildren: Whether to also dump children, false by default.
  ///   - includeTrivia: Add trivia to each dumped node, which the default
  ///   dump skips.
  ///   - converter: The location converter for the root of the tree. Adds
  ///   `[startLine:startCol...endLine:endCol]` to each node.
  ///   - mark: Adds `***` around the given node, intended to highlight it in
  ///   the dump.
  ///   - indentLevel: The starting indent level, 0 by default. Each level is 2
  ///   spaces.
  func debugDescription(includeChildren: Bool = false, includeTrivia: Bool = false,
                        converter: SourceLocationConverter? = nil, mark: SyntaxProtocol? = nil,
                        indentLevel: Int = 0) -> String {
    var str = ""
    debugWrite(to: &str, includeChildren: includeChildren, includeTrivia: includeTrivia,
               converter: converter, mark: mark, indentLevel: indentLevel)
    return str
  }

  private func debugWrite<Target: TextOutputStream>(to target: inout Target,
                                                    includeChildren: Bool, includeTrivia: Bool,
                                                    converter: SourceLocationConverter? = nil, mark: SyntaxProtocol? = nil,
                                                    indentLevel: Int) {
    if let mark = mark, self.id == mark.id {
      target.write("*** ")
    }

    if let token = Syntax(self).as(TokenSyntax.self) {
      target.write(String(describing: token.tokenKind))
      if includeTrivia {
        if let leadingTrivia = leadingTrivia, !leadingTrivia.isEmpty {
          target.write(" leadingTrivia=\(leadingTrivia.debugDescription)")
        }
        if let trailingTrivia = trailingTrivia, !trailingTrivia.isEmpty {
          target.write(" trailingTrivia=\(trailingTrivia.debugDescription)")
        }
      }
    } else {
      target.write(String(describing: syntaxNodeType))
    }

    let allChildren = children(viewMode: .all)
    if includeChildren {
      if !allChildren.isEmpty {
        target.write(" children=\(allChildren.count)")
      }
    }

    if let converter = converter {
      let range = sourceRange(converter: converter)
      target.write(" [\(range.start)...\(range.end)]")
    }

    if let tokenView = raw.tokenView, tokenView.presence == .missing {
      target.write(" MISSING")
    }

    if let mark = mark, self.id == mark.id {
      target.write(" ***")
    }

    if includeChildren {
      let childIndentLevel = indentLevel + 1
      for (num, child) in allChildren.enumerated() {
        target.write("\n")
        target.write(String(repeating: " ", count: childIndentLevel * 2))
        target.write("\(num): ")
        child.debugWrite(to: &target, includeChildren: includeChildren, includeTrivia: includeTrivia,
                         converter: converter, mark: mark, indentLevel: childIndentLevel)
      }
    }
  }
}

public protocol SyntaxCollection: SyntaxProtocol, BidirectionalCollection
  where Index == SyntaxChildrenIndex, Element: SyntaxProtocol {

  @_spi(RawSyntax)
  func _replacingLayout(_ layout: [RawSyntax?]) -> Self
}

extension SyntaxCollection {
  private var rawChildren: RawSyntaxChildren {
    // We know children in a syntax collection cannot be missing. So we can
    // use the low-level and faster RawSyntaxChildren collection instead of
    // NonNilRawSyntaxChildren.
    return RawSyntaxChildren(self.data.absoluteRaw)
  }

  public var count: Int {
    return rawChildren.count
  }

  public var startIndex: SyntaxChildrenIndex {
    return rawChildren.startIndex
  }
  public var endIndex: SyntaxChildrenIndex {
    return rawChildren.endIndex
  }

  public func index(after index: SyntaxChildrenIndex) -> SyntaxChildrenIndex {
    return rawChildren.index(after: index)
  }

  public func index(before index: SyntaxChildrenIndex) -> SyntaxChildrenIndex {
    return rawChildren.index(before: index)
  }

  public func distance(from start: SyntaxChildrenIndex, to end: SyntaxChildrenIndex)
      -> Int {
    return rawChildren.distance(from: start, to: end)
  }

  internal func _childData(at position: SyntaxChildrenIndex) -> SyntaxData {
    let (raw, info) = rawChildren[position]
    let absoluteRaw = AbsoluteRawSyntax(raw: raw!, info: info)
    let data = SyntaxData(absoluteRaw, parent: Syntax(self))
    return data
  }
}

extension SyntaxCollection {
  var layoutView: RawSyntaxLayoutView {
    data.raw.layoutView!
  }

  /// Creates a new `Self` by appending the provided syntax element
  /// to the children.
  ///
  /// - Parameter syntax: The element to append.
  /// - Returns: A new `Self` with that element appended to the end.
  public func appending(_ syntax: Element) -> Self {
    var newLayout = layoutView.formLayoutArray()
    newLayout.append(syntax.raw)
    return _replacingLayout(newLayout)
  }

  /// Creates a new `Self` by prepending the provided syntax element
  /// to the children.
  ///
  /// - Parameter syntax: The element to prepend.
  /// - Returns: A new `Self` with that element prepended to the beginning.
  public func prepending(_ syntax: Element) -> Self {
    return inserting(syntax, at: 0)
  }

  /// Creates a new `Self` by inserting the provided syntax element
  /// at the provided index in the children.
  ///
  /// - Parameters:
  ///   - syntax: The element to insert.
  ///   - index: The index at which to insert the element in the collection.
  ///
  /// - Returns: A new `Self` with that element appended to the end.
  public func inserting(_ syntax: Element,  at index: Int) -> Self {
    var newLayout = layoutView.formLayoutArray()
    /// Make sure the index is a valid insertion index (0 to 1 past the end)
    precondition((newLayout.startIndex...newLayout.endIndex).contains(index),
                 "inserting node at invalid index \(index)")
    newLayout.insert(syntax.raw, at: index)
    return _replacingLayout(newLayout)
  }

  /// Creates a new `Self` by replacing the syntax element
  /// at the provided index.
  ///
  /// - Parameters:
  ///   - index: The index at which to replace the element in the collection.
  ///   - syntax: The element to replace with.
  ///
  /// - Returns: A new `Self` with the new element at the provided index.
  public func replacing(childAt index: Int, with syntax: Element) -> Self {
    var newLayout = layoutView.formLayoutArray()
    /// Make sure the index is a valid index for replacing
    precondition((newLayout.startIndex..<newLayout.endIndex).contains(index),
                 "replacing node at invalid index \(index)")
    newLayout[index] = syntax.raw
    return _replacingLayout(newLayout)
  }

  /// Creates a new `Self` by removing the syntax element at the
  /// provided index.
  ///
  /// - Parameter index: The index of the element to remove from the collection.
  /// - Returns: A new `Self` with the element at the provided index
  ///            removed.
  public func removing(childAt index: Int) -> Self {
    var newLayout = layoutView.formLayoutArray()
    newLayout.remove(at: index)
    return _replacingLayout(newLayout)
  }

  /// Creates a new `Self` by removing the first element.
  ///
  /// - Returns: A new `Self` with the first element removed.
  public func removingFirst() -> Self {
    var newLayout = layoutView.formLayoutArray()
    newLayout.removeFirst()
    return _replacingLayout(newLayout)
  }

  /// Creates a new `Self` by removing the last element.
  ///
  /// - Returns: A new `Self` with the last element removed.
  public func removingLast() -> Self {
    var newLayout = layoutView.formLayoutArray()
    newLayout.removeLast()
    return _replacingLayout(newLayout)
  }
}

/// Sequence of tokens that are part of the provided Syntax node.
public struct TokenSequence: Sequence {
  public struct Iterator: IteratorProtocol {
    var nextToken: TokenSyntax?
    let endPosition: AbsolutePosition
    let viewMode: SyntaxTreeViewMode

    init(_ token: TokenSyntax?, endPosition: AbsolutePosition, viewMode: SyntaxTreeViewMode) {
      self.nextToken = token
      self.endPosition = endPosition
      self.viewMode = viewMode
    }

    public mutating func next() -> TokenSyntax? {
      guard let token = self.nextToken else { return nil }
      self.nextToken = token.nextToken(viewMode: viewMode)
      // Make sure we stop once we reach the end of the containing node.
      if let nextTok = self.nextToken, nextTok.position >= self.endPosition {
        self.nextToken = nil
      }
      return token
    }
  }

  let node: Syntax
  let viewMode: SyntaxTreeViewMode

  public init(_ node: Syntax, viewMode: SyntaxTreeViewMode) {
    self.node = node
    self.viewMode = viewMode
  }

  public func makeIterator() -> Iterator {
    return Iterator(node.firstToken(viewMode: viewMode), endPosition: node.endPosition, viewMode: viewMode)
  }

  public func reversed() -> ReversedTokenSequence {
    return ReversedTokenSequence(node, viewMode: viewMode)
  }
}

extension TokenSequence: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}

/// Reverse sequence of tokens that are part of the provided Syntax node.
public struct ReversedTokenSequence: Sequence {
  public struct Iterator: IteratorProtocol {
    var nextToken: TokenSyntax?
    let startPosition: AbsolutePosition
    let viewMode: SyntaxTreeViewMode

    init(_ token: TokenSyntax?, startPosition: AbsolutePosition, viewMode: SyntaxTreeViewMode) {
      self.nextToken = token
      self.startPosition = startPosition
      self.viewMode = viewMode
    }

    public mutating func next() -> TokenSyntax? {
      guard let token = self.nextToken else { return nil }
      self.nextToken = token.previousToken(viewMode: viewMode)
      // Make sure we stop once we went beyond the start of the containing node.
      if let nextTok = self.nextToken, nextTok.position < self.startPosition {
        self.nextToken = nil
      }
      return token
    }
  }

  let node: Syntax
  let viewMode: SyntaxTreeViewMode

  public init(_ node: Syntax, viewMode: SyntaxTreeViewMode) {
    self.node = node
    self.viewMode = viewMode
  }

  public func makeIterator() -> Iterator {
    return Iterator(node.lastToken(viewMode: viewMode), startPosition: node.position, viewMode: viewMode)
  }

  public func reversed() -> TokenSequence {
    return TokenSequence(node, viewMode: viewMode)
  }
}

extension ReversedTokenSequence: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}

/// Represents a node from the syntax tree.
///
/// This is a more efficient representation than `Syntax` because it avoids casts
/// to `Syntax` for representing the parent hierarchy.
/// It provides generic information, like the node's position, range, and
/// a unique `id`, while still allowing getting the associated `Syntax`
/// object if necessary.
///
/// `SyntaxParser` uses `SyntaxNode` to efficiently report which syntax nodes
/// got re-used during incremental re-parsing.
public struct SyntaxNode {
  let absoluteRaw: AbsoluteRawSyntax
  let parents: ArraySlice<AbsoluteRawSyntax>

  internal init(node: AbsoluteRawSyntax, parents: ArraySlice<AbsoluteRawSyntax>) {
    self.absoluteRaw = node
    self.parents = parents
  }

  var raw: RawSyntax {
    return absoluteRaw.raw
  }

  @_spi(RawSyntax)
  public func withUnsafeRawSyntax<R>(_ body: (RawSyntax) throws -> R) rethrows -> R {
    return try body(raw)
  }

  /// Converts this node to a `SyntaxData` object.
  ///
  /// This operation results in wrapping all of the node's parents into
  /// `SyntaxData` objects. There's a cost associated with it that should be
  /// taken into account before used inside performance critical code.
  internal var asSyntaxData: SyntaxData {
    if let parent = parent {
      return SyntaxData(absoluteRaw, parent: parent.asSyntax)
    } else {
      return SyntaxData.forRoot(absoluteRaw.raw)
    }
  }

  /// Converts this node to a `Syntax` object.
  ///
  /// This operation results in wrapping this node and all of its parents into
  /// `Syntax` objects. There's a cost associated with it that should be taken
  /// into account before used inside performance critical code.
  public var asSyntax: Syntax {
    return Syntax(self.asSyntaxData)
  }

  /// The parent of this syntax node, or `nil` if this node is the root.
  public var parent: SyntaxNode? {
    guard !parents.isEmpty else { return nil }
    return SyntaxNode(node: parents.last!, parents: parents.dropLast())
  }

  /// The absolute position of the starting point of this node.
  public var position: AbsolutePosition {
    return absoluteRaw.position
  }

  /// The end position of this node, including its trivia.
  public var endPosition: AbsolutePosition {
    return absoluteRaw.endPosition
  }

  /// The textual byte length of this node including leading and trailing trivia.
  public var byteSize: Int {
    return totalLength.utf8Length
  }

  /// The byte source range of this node including leading and trailing trivia.
  public var byteRange: ByteSourceRange {
    return ByteSourceRange(offset: position.utf8Offset, length: byteSize)
  }

  /// The length of this node including all of its trivia.
  public var totalLength: SourceLength {
    return raw.totalLength
  }
}

extension SyntaxNode: Identifiable {
  /// Returns a value representing the unique identity of the node.
  public var id: SyntaxIdentifier {
    return absoluteRaw.info.nodeId
  }
}

extension SyntaxNode: CustomStringConvertible, TextOutputStreamable {
  /// A source-accurate description of this node.
  public var description: String {
    return raw.description
  }

  /// Prints the raw value of this node to the provided stream.
  /// - Parameter stream: The stream to which to print the raw tree.
  public func write<Target>(to target: inout Target)
    where Target: TextOutputStream {
      raw.write(to: &target)
  }
}

/// Expose `recursiveDescription` on raw nodes for debugging purposes.
extension RawSyntaxNodeProtocol {
  /// Print this raw syntax node including all of its children.
  /// Intended for debugging purposes only.
  var recursiveDescription: String {
    return Syntax(raw: raw).recursiveDescription
  }
}
