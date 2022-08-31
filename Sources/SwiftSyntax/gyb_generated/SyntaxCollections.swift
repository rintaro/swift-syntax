//// Automatically Generated From SyntaxCollections.swift.gyb.
//// Do Not Edit Directly!
//===------------ SyntaxCollections.swift.gyb - Syntax Collection ---------===//
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



/// `CodeBlockItemListSyntax` represents a collection of one or more
/// `CodeBlockItemSyntax` nodes. CodeBlockItemListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct CodeBlockItemListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = CodeBlockItemSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `CodeBlockItemListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .codeBlockItemList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .codeBlockItemList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [CodeBlockItemSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.codeBlockItemList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `CodeBlockItemListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `CodeBlockItemListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return CodeBlockItemListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> CodeBlockItemSyntax {
    CodeBlockItemSyntax(self._childData(at: i))
  }
}

/// 
/// A collection of syntax nodes that occurred in the source code but
/// could not be used to form a valid syntax tree.
/// 
public struct UnexpectedNodesSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `UnexpectedNodesSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .unexpectedNodes else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .unexpectedNodes)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.unexpectedNodes,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `UnexpectedNodesSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `UnexpectedNodesSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return UnexpectedNodesSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// `TupleExprElementListSyntax` represents a collection of one or more
/// `TupleExprElementSyntax` nodes. TupleExprElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct TupleExprElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TupleExprElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `TupleExprElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .tupleExprElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .tupleExprElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TupleExprElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.tupleExprElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `TupleExprElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `TupleExprElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return TupleExprElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TupleExprElementSyntax {
    TupleExprElementSyntax(self._childData(at: i))
  }
}

/// `ArrayElementListSyntax` represents a collection of one or more
/// `ArrayElementSyntax` nodes. ArrayElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ArrayElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ArrayElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ArrayElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .arrayElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .arrayElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ArrayElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.arrayElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ArrayElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ArrayElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ArrayElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ArrayElementSyntax {
    ArrayElementSyntax(self._childData(at: i))
  }
}

/// `DictionaryElementListSyntax` represents a collection of one or more
/// `DictionaryElementSyntax` nodes. DictionaryElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct DictionaryElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = DictionaryElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `DictionaryElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .dictionaryElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .dictionaryElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [DictionaryElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.dictionaryElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `DictionaryElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `DictionaryElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return DictionaryElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> DictionaryElementSyntax {
    DictionaryElementSyntax(self._childData(at: i))
  }
}

/// `StringLiteralSegmentsSyntax` represents a collection of one or more
/// `Syntax` nodes. StringLiteralSegmentsSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct StringLiteralSegmentsSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `StringLiteralSegmentsSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .stringLiteralSegments else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .stringLiteralSegments)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.stringLiteralSegments,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `StringLiteralSegmentsSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `StringLiteralSegmentsSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return StringLiteralSegmentsSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// `DeclNameArgumentListSyntax` represents a collection of one or more
/// `DeclNameArgumentSyntax` nodes. DeclNameArgumentListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct DeclNameArgumentListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = DeclNameArgumentSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `DeclNameArgumentListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .declNameArgumentList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .declNameArgumentList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [DeclNameArgumentSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.declNameArgumentList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `DeclNameArgumentListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `DeclNameArgumentListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return DeclNameArgumentListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> DeclNameArgumentSyntax {
    DeclNameArgumentSyntax(self._childData(at: i))
  }
}

/// 
/// A list of expressions connected by operators. This list is contained
/// by a `SequenceExprSyntax`.
/// 
public struct ExprListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ExprSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ExprListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .exprList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .exprList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ExprSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.exprList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ExprListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ExprListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ExprListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ExprSyntax {
    ExprSyntax(self._childData(at: i))
  }
}

/// `ClosureCaptureItemListSyntax` represents a collection of one or more
/// `ClosureCaptureItemSyntax` nodes. ClosureCaptureItemListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ClosureCaptureItemListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ClosureCaptureItemSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ClosureCaptureItemListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .closureCaptureItemList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .closureCaptureItemList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ClosureCaptureItemSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.closureCaptureItemList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ClosureCaptureItemListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ClosureCaptureItemListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ClosureCaptureItemListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ClosureCaptureItemSyntax {
    ClosureCaptureItemSyntax(self._childData(at: i))
  }
}

/// `ClosureParamListSyntax` represents a collection of one or more
/// `ClosureParamSyntax` nodes. ClosureParamListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ClosureParamListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ClosureParamSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ClosureParamListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .closureParamList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .closureParamList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ClosureParamSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.closureParamList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ClosureParamListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ClosureParamListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ClosureParamListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ClosureParamSyntax {
    ClosureParamSyntax(self._childData(at: i))
  }
}

/// `MultipleTrailingClosureElementListSyntax` represents a collection of one or more
/// `MultipleTrailingClosureElementSyntax` nodes. MultipleTrailingClosureElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct MultipleTrailingClosureElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = MultipleTrailingClosureElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `MultipleTrailingClosureElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .multipleTrailingClosureElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .multipleTrailingClosureElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [MultipleTrailingClosureElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.multipleTrailingClosureElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `MultipleTrailingClosureElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `MultipleTrailingClosureElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return MultipleTrailingClosureElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> MultipleTrailingClosureElementSyntax {
    MultipleTrailingClosureElementSyntax(self._childData(at: i))
  }
}

/// `ObjcNameSyntax` represents a collection of one or more
/// `ObjcNamePieceSyntax` nodes. ObjcNameSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ObjcNameSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ObjcNamePieceSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ObjcNameSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .objcName else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .objcName)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ObjcNamePieceSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.objcName,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ObjcNameSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ObjcNameSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ObjcNameSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ObjcNamePieceSyntax {
    ObjcNamePieceSyntax(self._childData(at: i))
  }
}

/// `FunctionParameterListSyntax` represents a collection of one or more
/// `FunctionParameterSyntax` nodes. FunctionParameterListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct FunctionParameterListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = FunctionParameterSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `FunctionParameterListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .functionParameterList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .functionParameterList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [FunctionParameterSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.functionParameterList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `FunctionParameterListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `FunctionParameterListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return FunctionParameterListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> FunctionParameterSyntax {
    FunctionParameterSyntax(self._childData(at: i))
  }
}

/// `IfConfigClauseListSyntax` represents a collection of one or more
/// `IfConfigClauseSyntax` nodes. IfConfigClauseListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct IfConfigClauseListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = IfConfigClauseSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `IfConfigClauseListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .ifConfigClauseList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .ifConfigClauseList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [IfConfigClauseSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.ifConfigClauseList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `IfConfigClauseListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `IfConfigClauseListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return IfConfigClauseListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> IfConfigClauseSyntax {
    IfConfigClauseSyntax(self._childData(at: i))
  }
}

/// `InheritedTypeListSyntax` represents a collection of one or more
/// `InheritedTypeSyntax` nodes. InheritedTypeListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct InheritedTypeListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = InheritedTypeSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `InheritedTypeListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .inheritedTypeList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .inheritedTypeList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [InheritedTypeSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.inheritedTypeList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `InheritedTypeListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `InheritedTypeListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return InheritedTypeListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> InheritedTypeSyntax {
    InheritedTypeSyntax(self._childData(at: i))
  }
}

/// `MemberDeclListSyntax` represents a collection of one or more
/// `MemberDeclListItemSyntax` nodes. MemberDeclListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct MemberDeclListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = MemberDeclListItemSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `MemberDeclListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .memberDeclList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .memberDeclList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [MemberDeclListItemSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.memberDeclList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `MemberDeclListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `MemberDeclListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return MemberDeclListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> MemberDeclListItemSyntax {
    MemberDeclListItemSyntax(self._childData(at: i))
  }
}

/// `ModifierListSyntax` represents a collection of one or more
/// `DeclModifierSyntax` nodes. ModifierListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ModifierListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = DeclModifierSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ModifierListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .modifierList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .modifierList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [DeclModifierSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.modifierList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ModifierListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ModifierListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ModifierListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> DeclModifierSyntax {
    DeclModifierSyntax(self._childData(at: i))
  }
}

/// `AccessPathSyntax` represents a collection of one or more
/// `AccessPathComponentSyntax` nodes. AccessPathSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct AccessPathSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = AccessPathComponentSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `AccessPathSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .accessPath else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .accessPath)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [AccessPathComponentSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.accessPath,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `AccessPathSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `AccessPathSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return AccessPathSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> AccessPathComponentSyntax {
    AccessPathComponentSyntax(self._childData(at: i))
  }
}

/// `AccessorListSyntax` represents a collection of one or more
/// `AccessorDeclSyntax` nodes. AccessorListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct AccessorListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = AccessorDeclSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `AccessorListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .accessorList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .accessorList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [AccessorDeclSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.accessorList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `AccessorListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `AccessorListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return AccessorListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> AccessorDeclSyntax {
    AccessorDeclSyntax(self._childData(at: i))
  }
}

/// `PatternBindingListSyntax` represents a collection of one or more
/// `PatternBindingSyntax` nodes. PatternBindingListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct PatternBindingListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = PatternBindingSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `PatternBindingListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .patternBindingList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .patternBindingList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [PatternBindingSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.patternBindingList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `PatternBindingListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `PatternBindingListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return PatternBindingListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> PatternBindingSyntax {
    PatternBindingSyntax(self._childData(at: i))
  }
}

/// A collection of 0 or more `EnumCaseElement`s.
public struct EnumCaseElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = EnumCaseElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `EnumCaseElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .enumCaseElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .enumCaseElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [EnumCaseElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.enumCaseElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `EnumCaseElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `EnumCaseElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return EnumCaseElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> EnumCaseElementSyntax {
    EnumCaseElementSyntax(self._childData(at: i))
  }
}

/// `IdentifierListSyntax` represents a collection of one or more
/// `TokenSyntax` nodes. IdentifierListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct IdentifierListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TokenSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `IdentifierListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .identifierList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .identifierList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TokenSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.identifierList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `IdentifierListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `IdentifierListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return IdentifierListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TokenSyntax {
    TokenSyntax(self._childData(at: i))
  }
}

/// `PrecedenceGroupAttributeListSyntax` represents a collection of one or more
/// `Syntax` nodes. PrecedenceGroupAttributeListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct PrecedenceGroupAttributeListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `PrecedenceGroupAttributeListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .precedenceGroupAttributeList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .precedenceGroupAttributeList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.precedenceGroupAttributeList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `PrecedenceGroupAttributeListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `PrecedenceGroupAttributeListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return PrecedenceGroupAttributeListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// `PrecedenceGroupNameListSyntax` represents a collection of one or more
/// `PrecedenceGroupNameElementSyntax` nodes. PrecedenceGroupNameListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct PrecedenceGroupNameListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = PrecedenceGroupNameElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `PrecedenceGroupNameListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .precedenceGroupNameList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .precedenceGroupNameList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [PrecedenceGroupNameElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.precedenceGroupNameList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `PrecedenceGroupNameListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `PrecedenceGroupNameListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return PrecedenceGroupNameListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> PrecedenceGroupNameElementSyntax {
    PrecedenceGroupNameElementSyntax(self._childData(at: i))
  }
}

/// `TokenListSyntax` represents a collection of one or more
/// `TokenSyntax` nodes. TokenListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct TokenListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TokenSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `TokenListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .tokenList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .tokenList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TokenSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.tokenList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `TokenListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `TokenListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return TokenListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TokenSyntax {
    TokenSyntax(self._childData(at: i))
  }
}

/// `NonEmptyTokenListSyntax` represents a collection of one or more
/// `TokenSyntax` nodes. NonEmptyTokenListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct NonEmptyTokenListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TokenSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `NonEmptyTokenListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .nonEmptyTokenList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .nonEmptyTokenList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TokenSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.nonEmptyTokenList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `NonEmptyTokenListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `NonEmptyTokenListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return NonEmptyTokenListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TokenSyntax {
    TokenSyntax(self._childData(at: i))
  }
}

/// `AttributeListSyntax` represents a collection of one or more
/// `Syntax` nodes. AttributeListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct AttributeListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `AttributeListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .attributeList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .attributeList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.attributeList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `AttributeListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `AttributeListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return AttributeListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// 
/// A collection of arguments for the `@_specialize` attribute
/// 
public struct SpecializeAttributeSpecListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `SpecializeAttributeSpecListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .specializeAttributeSpecList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .specializeAttributeSpecList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.specializeAttributeSpecList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `SpecializeAttributeSpecListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `SpecializeAttributeSpecListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return SpecializeAttributeSpecListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// `ObjCSelectorSyntax` represents a collection of one or more
/// `ObjCSelectorPieceSyntax` nodes. ObjCSelectorSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ObjCSelectorSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ObjCSelectorPieceSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ObjCSelectorSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .objCSelector else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .objCSelector)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ObjCSelectorPieceSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.objCSelector,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ObjCSelectorSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ObjCSelectorSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ObjCSelectorSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ObjCSelectorPieceSyntax {
    ObjCSelectorPieceSyntax(self._childData(at: i))
  }
}

/// `DifferentiabilityParamListSyntax` represents a collection of one or more
/// `DifferentiabilityParamSyntax` nodes. DifferentiabilityParamListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct DifferentiabilityParamListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = DifferentiabilityParamSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `DifferentiabilityParamListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .differentiabilityParamList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .differentiabilityParamList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [DifferentiabilityParamSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.differentiabilityParamList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `DifferentiabilityParamListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `DifferentiabilityParamListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return DifferentiabilityParamListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> DifferentiabilityParamSyntax {
    DifferentiabilityParamSyntax(self._childData(at: i))
  }
}

/// `BackDeployVersionListSyntax` represents a collection of one or more
/// `BackDeployVersionArgumentSyntax` nodes. BackDeployVersionListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct BackDeployVersionListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = BackDeployVersionArgumentSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `BackDeployVersionListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .backDeployVersionList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .backDeployVersionList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [BackDeployVersionArgumentSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.backDeployVersionList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `BackDeployVersionListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `BackDeployVersionListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return BackDeployVersionListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> BackDeployVersionArgumentSyntax {
    BackDeployVersionArgumentSyntax(self._childData(at: i))
  }
}

/// `SwitchCaseListSyntax` represents a collection of one or more
/// `Syntax` nodes. SwitchCaseListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct SwitchCaseListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = Syntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `SwitchCaseListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .switchCaseList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .switchCaseList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [Syntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.switchCaseList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `SwitchCaseListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `SwitchCaseListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return SwitchCaseListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> Syntax {
    Syntax(self._childData(at: i))
  }
}

/// `CatchClauseListSyntax` represents a collection of one or more
/// `CatchClauseSyntax` nodes. CatchClauseListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct CatchClauseListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = CatchClauseSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `CatchClauseListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .catchClauseList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .catchClauseList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [CatchClauseSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.catchClauseList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `CatchClauseListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `CatchClauseListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return CatchClauseListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> CatchClauseSyntax {
    CatchClauseSyntax(self._childData(at: i))
  }
}

/// `CaseItemListSyntax` represents a collection of one or more
/// `CaseItemSyntax` nodes. CaseItemListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct CaseItemListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = CaseItemSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `CaseItemListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .caseItemList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .caseItemList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [CaseItemSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.caseItemList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `CaseItemListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `CaseItemListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return CaseItemListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> CaseItemSyntax {
    CaseItemSyntax(self._childData(at: i))
  }
}

/// `CatchItemListSyntax` represents a collection of one or more
/// `CatchItemSyntax` nodes. CatchItemListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct CatchItemListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = CatchItemSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `CatchItemListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .catchItemList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .catchItemList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [CatchItemSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.catchItemList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `CatchItemListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `CatchItemListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return CatchItemListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> CatchItemSyntax {
    CatchItemSyntax(self._childData(at: i))
  }
}

/// `ConditionElementListSyntax` represents a collection of one or more
/// `ConditionElementSyntax` nodes. ConditionElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct ConditionElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = ConditionElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `ConditionElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .conditionElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .conditionElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [ConditionElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.conditionElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `ConditionElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `ConditionElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return ConditionElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> ConditionElementSyntax {
    ConditionElementSyntax(self._childData(at: i))
  }
}

/// `GenericRequirementListSyntax` represents a collection of one or more
/// `GenericRequirementSyntax` nodes. GenericRequirementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct GenericRequirementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = GenericRequirementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `GenericRequirementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .genericRequirementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .genericRequirementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [GenericRequirementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.genericRequirementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `GenericRequirementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `GenericRequirementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return GenericRequirementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> GenericRequirementSyntax {
    GenericRequirementSyntax(self._childData(at: i))
  }
}

/// `GenericParameterListSyntax` represents a collection of one or more
/// `GenericParameterSyntax` nodes. GenericParameterListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct GenericParameterListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = GenericParameterSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `GenericParameterListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .genericParameterList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .genericParameterList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [GenericParameterSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.genericParameterList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `GenericParameterListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `GenericParameterListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return GenericParameterListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> GenericParameterSyntax {
    GenericParameterSyntax(self._childData(at: i))
  }
}

/// `PrimaryAssociatedTypeListSyntax` represents a collection of one or more
/// `PrimaryAssociatedTypeSyntax` nodes. PrimaryAssociatedTypeListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct PrimaryAssociatedTypeListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = PrimaryAssociatedTypeSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `PrimaryAssociatedTypeListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .primaryAssociatedTypeList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .primaryAssociatedTypeList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [PrimaryAssociatedTypeSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.primaryAssociatedTypeList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `PrimaryAssociatedTypeListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `PrimaryAssociatedTypeListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return PrimaryAssociatedTypeListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> PrimaryAssociatedTypeSyntax {
    PrimaryAssociatedTypeSyntax(self._childData(at: i))
  }
}

/// `CompositionTypeElementListSyntax` represents a collection of one or more
/// `CompositionTypeElementSyntax` nodes. CompositionTypeElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct CompositionTypeElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = CompositionTypeElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `CompositionTypeElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .compositionTypeElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .compositionTypeElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [CompositionTypeElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.compositionTypeElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `CompositionTypeElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `CompositionTypeElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return CompositionTypeElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> CompositionTypeElementSyntax {
    CompositionTypeElementSyntax(self._childData(at: i))
  }
}

/// `TupleTypeElementListSyntax` represents a collection of one or more
/// `TupleTypeElementSyntax` nodes. TupleTypeElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct TupleTypeElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TupleTypeElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `TupleTypeElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .tupleTypeElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .tupleTypeElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TupleTypeElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.tupleTypeElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `TupleTypeElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `TupleTypeElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return TupleTypeElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TupleTypeElementSyntax {
    TupleTypeElementSyntax(self._childData(at: i))
  }
}

/// `GenericArgumentListSyntax` represents a collection of one or more
/// `GenericArgumentSyntax` nodes. GenericArgumentListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct GenericArgumentListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = GenericArgumentSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `GenericArgumentListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .genericArgumentList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .genericArgumentList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [GenericArgumentSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.genericArgumentList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `GenericArgumentListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `GenericArgumentListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return GenericArgumentListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> GenericArgumentSyntax {
    GenericArgumentSyntax(self._childData(at: i))
  }
}

/// `TuplePatternElementListSyntax` represents a collection of one or more
/// `TuplePatternElementSyntax` nodes. TuplePatternElementListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct TuplePatternElementListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = TuplePatternElementSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `TuplePatternElementListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .tuplePatternElementList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .tuplePatternElementList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [TuplePatternElementSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.tuplePatternElementList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `TuplePatternElementListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `TuplePatternElementListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return TuplePatternElementListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> TuplePatternElementSyntax {
    TuplePatternElementSyntax(self._childData(at: i))
  }
}

/// `AvailabilitySpecListSyntax` represents a collection of one or more
/// `AvailabilityArgumentSyntax` nodes. AvailabilitySpecListSyntax behaves
/// as a regular Swift collection, and has accessors that return new
/// versions of the collection with different children.
public struct AvailabilitySpecListSyntax: SyntaxCollection, SyntaxHashable {
  public typealias Element = AvailabilityArgumentSyntax

  public let _syntaxNode: Syntax

  /// Converts the given `Syntax` node to a `AvailabilitySpecListSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  public init?(_ syntax: Syntax) {
    guard syntax.raw.kind == .availabilitySpecList else { return nil }
    self._syntaxNode = syntax
  }

  /// Creates a Syntax node from the provided root and data. This assumes 
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  internal init(_ data: SyntaxData) {
    assert(data.raw.kind == .availabilitySpecList)
    self._syntaxNode = Syntax(data)
  }

  public init(_ children: [AvailabilityArgumentSyntax]) {
    let raw = RawSyntax.makeLayout(kind: SyntaxKind.availabilitySpecList,
      from: children.map { $0.raw }, arena: .default)
    let data = SyntaxData.forRoot(raw)
    self.init(data)
  }

  public var syntaxNodeType: SyntaxProtocol.Type {
    return Swift.type(of: self)
  }

  /// Creates a new `AvailabilitySpecListSyntax` by replacing the underlying layout with
  /// a different set of raw syntax nodes.
  ///
  /// - Parameter layout: The new list of raw syntax nodes underlying this
  ///                     collection.
  /// - Returns: A new `AvailabilitySpecListSyntax` with the new layout underlying it.
  @_spi(RawSyntax)
  public func _replacingLayout(_ layout: [RawSyntax?]) -> Self {
    return AvailabilitySpecListSyntax(data.replacingLayout(with: layout))
  }

  public subscript(i: Index) -> AvailabilityArgumentSyntax {
    AvailabilityArgumentSyntax(self._childData(at: i))
  }
}

extension CodeBlockItemListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension UnexpectedNodesSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension TupleExprElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ArrayElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension DictionaryElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension StringLiteralSegmentsSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension DeclNameArgumentListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ExprListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ClosureCaptureItemListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ClosureParamListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension MultipleTrailingClosureElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ObjcNameSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension FunctionParameterListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension IfConfigClauseListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension InheritedTypeListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension MemberDeclListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ModifierListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension AccessPathSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension AccessorListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension PatternBindingListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension EnumCaseElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension IdentifierListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension PrecedenceGroupAttributeListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension PrecedenceGroupNameListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension TokenListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension NonEmptyTokenListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension AttributeListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension SpecializeAttributeSpecListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ObjCSelectorSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension DifferentiabilityParamListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension BackDeployVersionListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension SwitchCaseListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension CatchClauseListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension CaseItemListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension CatchItemListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension ConditionElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension GenericRequirementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension GenericParameterListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension PrimaryAssociatedTypeListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension CompositionTypeElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension TupleTypeElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension GenericArgumentListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension TuplePatternElementListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
extension AvailabilitySpecListSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, unlabeledChildren: self.map{ $0 })
  }
}
