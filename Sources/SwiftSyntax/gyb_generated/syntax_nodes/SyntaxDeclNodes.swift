//// Automatically Generated From SyntaxNodes.swift.gyb.
//// Do Not Edit Directly!
//===------------ SyntaxNodes.swift - Syntax Node definitions -------------===//
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



// MARK: - UnknownDeclSyntax

public struct UnknownDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawUnknownDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `UnknownDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `UnknownDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }
}

extension UnknownDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
    ])
  }
}

// MARK: - TypealiasDeclSyntax

public struct TypealiasDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case typealiasKeyword
    case identifier
    case genericParameterClause
    case initializer
    case genericWhereClause
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawTypealiasDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `TypealiasDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `TypealiasDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> TypealiasDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> TypealiasDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var typealiasKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.typealiasKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withTypealiasKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `typealiasKeyword` replaced.
  /// - param newChild: The new `typealiasKeyword` to replace the node's
  ///                   current `typealiasKeyword`, if present.
  public func withTypealiasKeyword(
    _ newChild: TokenSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .typealiasKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.typealiasKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var initializer: TypeInitializerClauseSyntax {
    get {
      let childData = data.child(at: Cursor.initializer.rawValue)
      return TypeInitializerClauseSyntax(data: childData!)
    }
    set(value) {
      self = withInitializer(value)
    }
  }

  /// Returns a copy of the receiver with its `initializer` replaced.
  /// - param newChild: The new `initializer` to replace the node's
  ///                   current `initializer`, if present.
  public func withInitializer(
    _ newChild: TypeInitializerClauseSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeInitializerClauseSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.initializer.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> TypealiasDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension TypealiasDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "typealiasKeyword": Syntax(typealiasKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "initializer": Syntax(initializer).asProtocol(SyntaxProtocol.self),
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - AssociatedtypeDeclSyntax

public struct AssociatedtypeDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case associatedtypeKeyword
    case identifier
    case inheritanceClause
    case initializer
    case genericWhereClause
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawAssociatedtypeDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `AssociatedtypeDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `AssociatedtypeDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> AssociatedtypeDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> AssociatedtypeDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var associatedtypeKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.associatedtypeKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withAssociatedtypeKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `associatedtypeKeyword` replaced.
  /// - param newChild: The new `associatedtypeKeyword` to replace the node's
  ///                   current `associatedtypeKeyword`, if present.
  public func withAssociatedtypeKeyword(
    _ newChild: TokenSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .associatedtypeKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.associatedtypeKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var initializer: TypeInitializerClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.initializer.rawValue)
      return childData.map { TypeInitializerClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInitializer(value)
    }
  }

  /// Returns a copy of the receiver with its `initializer` replaced.
  /// - param newChild: The new `initializer` to replace the node's
  ///                   current `initializer`, if present.
  public func withInitializer(
    _ newChild: TypeInitializerClauseSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.initializer.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> AssociatedtypeDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension AssociatedtypeDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "associatedtypeKeyword": Syntax(associatedtypeKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "initializer": initializer.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - IfConfigDeclSyntax

public struct IfConfigDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case clauses
    case poundEndif
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawIfConfigDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `IfConfigDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `IfConfigDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var clauses: IfConfigClauseListSyntax {
    get {
      let childData = data.child(at: Cursor.clauses.rawValue)
      return IfConfigClauseListSyntax(data: childData!)
    }
    set(value) {
      self = withClauses(value)
    }
  }

  /// Adds the provided `Clause` to the node's `clauses`
  /// collection.
  /// - param element: The new `Clause` to add to the node's
  ///                  `clauses` collection.
  /// - returns: A copy of the receiver with the provided `Clause`
  ///            appended to its `clauses` collection.
  public func addClause(_ element: IfConfigClauseSyntax) -> IfConfigDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.clauses.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .ifConfigClauseList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.clauses.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `clauses` replaced.
  /// - param newChild: The new `clauses` to replace the node's
  ///                   current `clauses`, if present.
  public func withClauses(
    _ newChild: IfConfigClauseListSyntax?) -> IfConfigDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawIfConfigClauseListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.clauses.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var poundEndif: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.poundEndif.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPoundEndif(value)
    }
  }

  /// Returns a copy of the receiver with its `poundEndif` replaced.
  /// - param newChild: The new `poundEndif` to replace the node's
  ///                   current `poundEndif`, if present.
  public func withPoundEndif(
    _ newChild: TokenSyntax?) -> IfConfigDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .poundEndifKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.poundEndif.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension IfConfigDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "clauses": Syntax(clauses).asProtocol(SyntaxProtocol.self),
      "poundEndif": Syntax(poundEndif).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - PoundErrorDeclSyntax

public struct PoundErrorDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case poundError
    case leftParen
    case message
    case rightParen
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawPoundErrorDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `PoundErrorDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `PoundErrorDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var poundError: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.poundError.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPoundError(value)
    }
  }

  /// Returns a copy of the receiver with its `poundError` replaced.
  /// - param newChild: The new `poundError` to replace the node's
  ///                   current `poundError`, if present.
  public func withPoundError(
    _ newChild: TokenSyntax?) -> PoundErrorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .poundErrorKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.poundError.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var leftParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftParen(value)
    }
  }

  /// Returns a copy of the receiver with its `leftParen` replaced.
  /// - param newChild: The new `leftParen` to replace the node's
  ///                   current `leftParen`, if present.
  public func withLeftParen(
    _ newChild: TokenSyntax?) -> PoundErrorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var message: StringLiteralExprSyntax {
    get {
      let childData = data.child(at: Cursor.message.rawValue)
      return StringLiteralExprSyntax(data: childData!)
    }
    set(value) {
      self = withMessage(value)
    }
  }

  /// Returns a copy of the receiver with its `message` replaced.
  /// - param newChild: The new `message` to replace the node's
  ///                   current `message`, if present.
  public func withMessage(
    _ newChild: StringLiteralExprSyntax?) -> PoundErrorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawStringLiteralExprSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.message.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightParen(value)
    }
  }

  /// Returns a copy of the receiver with its `rightParen` replaced.
  /// - param newChild: The new `rightParen` to replace the node's
  ///                   current `rightParen`, if present.
  public func withRightParen(
    _ newChild: TokenSyntax?) -> PoundErrorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension PoundErrorDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "poundError": Syntax(poundError).asProtocol(SyntaxProtocol.self),
      "leftParen": Syntax(leftParen).asProtocol(SyntaxProtocol.self),
      "message": Syntax(message).asProtocol(SyntaxProtocol.self),
      "rightParen": Syntax(rightParen).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - PoundWarningDeclSyntax

public struct PoundWarningDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case poundWarning
    case leftParen
    case message
    case rightParen
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawPoundWarningDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `PoundWarningDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `PoundWarningDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var poundWarning: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.poundWarning.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPoundWarning(value)
    }
  }

  /// Returns a copy of the receiver with its `poundWarning` replaced.
  /// - param newChild: The new `poundWarning` to replace the node's
  ///                   current `poundWarning`, if present.
  public func withPoundWarning(
    _ newChild: TokenSyntax?) -> PoundWarningDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .poundWarningKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.poundWarning.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var leftParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftParen(value)
    }
  }

  /// Returns a copy of the receiver with its `leftParen` replaced.
  /// - param newChild: The new `leftParen` to replace the node's
  ///                   current `leftParen`, if present.
  public func withLeftParen(
    _ newChild: TokenSyntax?) -> PoundWarningDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var message: StringLiteralExprSyntax {
    get {
      let childData = data.child(at: Cursor.message.rawValue)
      return StringLiteralExprSyntax(data: childData!)
    }
    set(value) {
      self = withMessage(value)
    }
  }

  /// Returns a copy of the receiver with its `message` replaced.
  /// - param newChild: The new `message` to replace the node's
  ///                   current `message`, if present.
  public func withMessage(
    _ newChild: StringLiteralExprSyntax?) -> PoundWarningDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawStringLiteralExprSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.message.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightParen(value)
    }
  }

  /// Returns a copy of the receiver with its `rightParen` replaced.
  /// - param newChild: The new `rightParen` to replace the node's
  ///                   current `rightParen`, if present.
  public func withRightParen(
    _ newChild: TokenSyntax?) -> PoundWarningDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension PoundWarningDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "poundWarning": Syntax(poundWarning).asProtocol(SyntaxProtocol.self),
      "leftParen": Syntax(leftParen).asProtocol(SyntaxProtocol.self),
      "message": Syntax(message).asProtocol(SyntaxProtocol.self),
      "rightParen": Syntax(rightParen).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - PoundSourceLocationSyntax

public struct PoundSourceLocationSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case poundSourceLocation
    case leftParen
    case args
    case rightParen
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawPoundSourceLocationSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `PoundSourceLocationSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `PoundSourceLocationSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var poundSourceLocation: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.poundSourceLocation.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPoundSourceLocation(value)
    }
  }

  /// Returns a copy of the receiver with its `poundSourceLocation` replaced.
  /// - param newChild: The new `poundSourceLocation` to replace the node's
  ///                   current `poundSourceLocation`, if present.
  public func withPoundSourceLocation(
    _ newChild: TokenSyntax?) -> PoundSourceLocationSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .poundSourceLocationKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.poundSourceLocation.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var leftParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftParen(value)
    }
  }

  /// Returns a copy of the receiver with its `leftParen` replaced.
  /// - param newChild: The new `leftParen` to replace the node's
  ///                   current `leftParen`, if present.
  public func withLeftParen(
    _ newChild: TokenSyntax?) -> PoundSourceLocationSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var args: PoundSourceLocationArgsSyntax? {
    get {
      let childData = data.child(at: Cursor.args.rawValue)
      return childData.map { PoundSourceLocationArgsSyntax(data: $0) }
    }
    set(value) {
      self = withArgs(value)
    }
  }

  /// Returns a copy of the receiver with its `args` replaced.
  /// - param newChild: The new `args` to replace the node's
  ///                   current `args`, if present.
  public func withArgs(
    _ newChild: PoundSourceLocationArgsSyntax?) -> PoundSourceLocationSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.args.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightParen: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightParen.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightParen(value)
    }
  }

  /// Returns a copy of the receiver with its `rightParen` replaced.
  /// - param newChild: The new `rightParen` to replace the node's
  ///                   current `rightParen`, if present.
  public func withRightParen(
    _ newChild: TokenSyntax?) -> PoundSourceLocationSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension PoundSourceLocationSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "poundSourceLocation": Syntax(poundSourceLocation).asProtocol(SyntaxProtocol.self),
      "leftParen": Syntax(leftParen).asProtocol(SyntaxProtocol.self),
      "args": args.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "rightParen": Syntax(rightParen).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ClassDeclSyntax

public struct ClassDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case classKeyword
    case identifier
    case genericParameterClause
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawClassDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ClassDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ClassDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> ClassDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> ClassDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var classKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.classKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withClassKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `classKeyword` replaced.
  /// - param newChild: The new `classKeyword` to replace the node's
  ///                   current `classKeyword`, if present.
  public func withClassKeyword(
    _ newChild: TokenSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .classKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.classKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> ClassDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ClassDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "classKeyword": Syntax(classKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ActorDeclSyntax

public struct ActorDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case actorKeyword
    case identifier
    case genericParameterClause
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawActorDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ActorDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ActorDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> ActorDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> ActorDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var actorKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.actorKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withActorKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `actorKeyword` replaced.
  /// - param newChild: The new `actorKeyword` to replace the node's
  ///                   current `actorKeyword`, if present.
  public func withActorKeyword(
    _ newChild: TokenSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .contextualKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.actorKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> ActorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ActorDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "actorKeyword": Syntax(actorKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - StructDeclSyntax

public struct StructDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case structKeyword
    case identifier
    case genericParameterClause
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawStructDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `StructDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `StructDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> StructDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> StructDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var structKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.structKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withStructKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `structKeyword` replaced.
  /// - param newChild: The new `structKeyword` to replace the node's
  ///                   current `structKeyword`, if present.
  public func withStructKeyword(
    _ newChild: TokenSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .structKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.structKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> StructDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension StructDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "structKeyword": Syntax(structKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ProtocolDeclSyntax

public struct ProtocolDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case protocolKeyword
    case identifier
    case primaryAssociatedTypeClause
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawProtocolDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ProtocolDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ProtocolDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> ProtocolDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> ProtocolDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var protocolKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.protocolKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withProtocolKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `protocolKeyword` replaced.
  /// - param newChild: The new `protocolKeyword` to replace the node's
  ///                   current `protocolKeyword`, if present.
  public func withProtocolKeyword(
    _ newChild: TokenSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .protocolKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.protocolKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var primaryAssociatedTypeClause: PrimaryAssociatedTypeClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.primaryAssociatedTypeClause.rawValue)
      return childData.map { PrimaryAssociatedTypeClauseSyntax(data: $0) }
    }
    set(value) {
      self = withPrimaryAssociatedTypeClause(value)
    }
  }

  /// Returns a copy of the receiver with its `primaryAssociatedTypeClause` replaced.
  /// - param newChild: The new `primaryAssociatedTypeClause` to replace the node's
  ///                   current `primaryAssociatedTypeClause`, if present.
  public func withPrimaryAssociatedTypeClause(
    _ newChild: PrimaryAssociatedTypeClauseSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.primaryAssociatedTypeClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> ProtocolDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ProtocolDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "protocolKeyword": Syntax(protocolKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "primaryAssociatedTypeClause": primaryAssociatedTypeClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ExtensionDeclSyntax

public struct ExtensionDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case extensionKeyword
    case extendedType
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawExtensionDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ExtensionDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ExtensionDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> ExtensionDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> ExtensionDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var extensionKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.extensionKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withExtensionKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `extensionKeyword` replaced.
  /// - param newChild: The new `extensionKeyword` to replace the node's
  ///                   current `extensionKeyword`, if present.
  public func withExtensionKeyword(
    _ newChild: TokenSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .extensionKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.extensionKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var extendedType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.extendedType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withExtendedType(value)
    }
  }

  /// Returns a copy of the receiver with its `extendedType` replaced.
  /// - param newChild: The new `extendedType` to replace the node's
  ///                   current `extendedType`, if present.
  public func withExtendedType(
    _ newChild: TypeSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.extendedType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> ExtensionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ExtensionDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "extensionKeyword": Syntax(extensionKeyword).asProtocol(SyntaxProtocol.self),
      "extendedType": Syntax(extendedType).asProtocol(SyntaxProtocol.self),
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - FunctionDeclSyntax

public struct FunctionDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case funcKeyword
    case identifier
    case genericParameterClause
    case signature
    case genericWhereClause
    case body
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawFunctionDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `FunctionDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `FunctionDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> FunctionDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> FunctionDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var funcKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.funcKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withFuncKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `funcKeyword` replaced.
  /// - param newChild: The new `funcKeyword` to replace the node's
  ///                   current `funcKeyword`, if present.
  public func withFuncKeyword(
    _ newChild: TokenSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .funcKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.funcKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var signature: FunctionSignatureSyntax {
    get {
      let childData = data.child(at: Cursor.signature.rawValue)
      return FunctionSignatureSyntax(data: childData!)
    }
    set(value) {
      self = withSignature(value)
    }
  }

  /// Returns a copy of the receiver with its `signature` replaced.
  /// - param newChild: The new `signature` to replace the node's
  ///                   current `signature`, if present.
  public func withSignature(
    _ newChild: FunctionSignatureSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawFunctionSignatureSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.signature.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var body: CodeBlockSyntax? {
    get {
      let childData = data.child(at: Cursor.body.rawValue)
      return childData.map { CodeBlockSyntax(data: $0) }
    }
    set(value) {
      self = withBody(value)
    }
  }

  /// Returns a copy of the receiver with its `body` replaced.
  /// - param newChild: The new `body` to replace the node's
  ///                   current `body`, if present.
  public func withBody(
    _ newChild: CodeBlockSyntax?) -> FunctionDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.body.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension FunctionDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "funcKeyword": Syntax(funcKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "signature": Syntax(signature).asProtocol(SyntaxProtocol.self),
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "body": body.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - InitializerDeclSyntax

public struct InitializerDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case initKeyword
    case optionalMark
    case genericParameterClause
    case signature
    case genericWhereClause
    case body
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawInitializerDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `InitializerDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `InitializerDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> InitializerDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> InitializerDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var initKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.initKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withInitKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `initKeyword` replaced.
  /// - param newChild: The new `initKeyword` to replace the node's
  ///                   current `initKeyword`, if present.
  public func withInitKeyword(
    _ newChild: TokenSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .initKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.initKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var optionalMark: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.optionalMark.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withOptionalMark(value)
    }
  }

  /// Returns a copy of the receiver with its `optionalMark` replaced.
  /// - param newChild: The new `optionalMark` to replace the node's
  ///                   current `optionalMark`, if present.
  public func withOptionalMark(
    _ newChild: TokenSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.optionalMark.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var signature: FunctionSignatureSyntax {
    get {
      let childData = data.child(at: Cursor.signature.rawValue)
      return FunctionSignatureSyntax(data: childData!)
    }
    set(value) {
      self = withSignature(value)
    }
  }

  /// Returns a copy of the receiver with its `signature` replaced.
  /// - param newChild: The new `signature` to replace the node's
  ///                   current `signature`, if present.
  public func withSignature(
    _ newChild: FunctionSignatureSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawFunctionSignatureSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.signature.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var body: CodeBlockSyntax? {
    get {
      let childData = data.child(at: Cursor.body.rawValue)
      return childData.map { CodeBlockSyntax(data: $0) }
    }
    set(value) {
      self = withBody(value)
    }
  }

  /// Returns a copy of the receiver with its `body` replaced.
  /// - param newChild: The new `body` to replace the node's
  ///                   current `body`, if present.
  public func withBody(
    _ newChild: CodeBlockSyntax?) -> InitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.body.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension InitializerDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "initKeyword": Syntax(initKeyword).asProtocol(SyntaxProtocol.self),
      "optionalMark": optionalMark.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "signature": Syntax(signature).asProtocol(SyntaxProtocol.self),
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "body": body.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - DeinitializerDeclSyntax

public struct DeinitializerDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case deinitKeyword
    case body
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawDeinitializerDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `DeinitializerDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `DeinitializerDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> DeinitializerDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> DeinitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> DeinitializerDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> DeinitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var deinitKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.deinitKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withDeinitKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `deinitKeyword` replaced.
  /// - param newChild: The new `deinitKeyword` to replace the node's
  ///                   current `deinitKeyword`, if present.
  public func withDeinitKeyword(
    _ newChild: TokenSyntax?) -> DeinitializerDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .deinitKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.deinitKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var body: CodeBlockSyntax? {
    get {
      let childData = data.child(at: Cursor.body.rawValue)
      return childData.map { CodeBlockSyntax(data: $0) }
    }
    set(value) {
      self = withBody(value)
    }
  }

  /// Returns a copy of the receiver with its `body` replaced.
  /// - param newChild: The new `body` to replace the node's
  ///                   current `body`, if present.
  public func withBody(
    _ newChild: CodeBlockSyntax?) -> DeinitializerDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.body.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension DeinitializerDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "deinitKeyword": Syntax(deinitKeyword).asProtocol(SyntaxProtocol.self),
      "body": body.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - SubscriptDeclSyntax

public struct SubscriptDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case subscriptKeyword
    case genericParameterClause
    case indices
    case result
    case genericWhereClause
    case accessor
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawSubscriptDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `SubscriptDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `SubscriptDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> SubscriptDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> SubscriptDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var subscriptKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.subscriptKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withSubscriptKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `subscriptKeyword` replaced.
  /// - param newChild: The new `subscriptKeyword` to replace the node's
  ///                   current `subscriptKeyword`, if present.
  public func withSubscriptKeyword(
    _ newChild: TokenSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .subscriptKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.subscriptKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericParameterClause: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameterClause.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameterClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameterClause` replaced.
  /// - param newChild: The new `genericParameterClause` to replace the node's
  ///                   current `genericParameterClause`, if present.
  public func withGenericParameterClause(
    _ newChild: GenericParameterClauseSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameterClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var indices: ParameterClauseSyntax {
    get {
      let childData = data.child(at: Cursor.indices.rawValue)
      return ParameterClauseSyntax(data: childData!)
    }
    set(value) {
      self = withIndices(value)
    }
  }

  /// Returns a copy of the receiver with its `indices` replaced.
  /// - param newChild: The new `indices` to replace the node's
  ///                   current `indices`, if present.
  public func withIndices(
    _ newChild: ParameterClauseSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawParameterClauseSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.indices.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var result: ReturnClauseSyntax {
    get {
      let childData = data.child(at: Cursor.result.rawValue)
      return ReturnClauseSyntax(data: childData!)
    }
    set(value) {
      self = withResult(value)
    }
  }

  /// Returns a copy of the receiver with its `result` replaced.
  /// - param newChild: The new `result` to replace the node's
  ///                   current `result`, if present.
  public func withResult(
    _ newChild: ReturnClauseSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawReturnClauseSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.result.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var accessor: Syntax? {
    get {
      let childData = data.child(at: Cursor.accessor.rawValue)
      return childData.map { Syntax(data: $0) }
    }
    set(value) {
      self = withAccessor(value)
    }
  }

  /// Returns a copy of the receiver with its `accessor` replaced.
  /// - param newChild: The new `accessor` to replace the node's
  ///                   current `accessor`, if present.
  public func withAccessor(
    _ newChild: Syntax?) -> SubscriptDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.accessor.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension SubscriptDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "subscriptKeyword": Syntax(subscriptKeyword).asProtocol(SyntaxProtocol.self),
      "genericParameterClause": genericParameterClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "indices": Syntax(indices).asProtocol(SyntaxProtocol.self),
      "result": Syntax(result).asProtocol(SyntaxProtocol.self),
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "accessor": accessor.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - ImportDeclSyntax

public struct ImportDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case importTok
    case importKind
    case path
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawImportDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ImportDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ImportDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> ImportDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> ImportDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> ImportDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> ImportDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var importTok: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.importTok.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withImportTok(value)
    }
  }

  /// Returns a copy of the receiver with its `importTok` replaced.
  /// - param newChild: The new `importTok` to replace the node's
  ///                   current `importTok`, if present.
  public func withImportTok(
    _ newChild: TokenSyntax?) -> ImportDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .importKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.importTok.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var importKind: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.importKind.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withImportKind(value)
    }
  }

  /// Returns a copy of the receiver with its `importKind` replaced.
  /// - param newChild: The new `importKind` to replace the node's
  ///                   current `importKind`, if present.
  public func withImportKind(
    _ newChild: TokenSyntax?) -> ImportDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.importKind.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var path: AccessPathSyntax {
    get {
      let childData = data.child(at: Cursor.path.rawValue)
      return AccessPathSyntax(data: childData!)
    }
    set(value) {
      self = withPath(value)
    }
  }

  /// Adds the provided `PathComponent` to the node's `path`
  /// collection.
  /// - param element: The new `PathComponent` to add to the node's
  ///                  `path` collection.
  /// - returns: A copy of the receiver with the provided `PathComponent`
  ///            appended to its `path` collection.
  public func addPathComponent(_ element: AccessPathComponentSyntax) -> ImportDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.path.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .accessPath, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.path.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `path` replaced.
  /// - param newChild: The new `path` to replace the node's
  ///                   current `path`, if present.
  public func withPath(
    _ newChild: AccessPathSyntax?) -> ImportDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawAccessPathSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.path.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ImportDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "importTok": Syntax(importTok).asProtocol(SyntaxProtocol.self),
      "importKind": importKind.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "path": Syntax(path).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - AccessorDeclSyntax

public struct AccessorDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifier
    case accessorKind
    case parameter
    case asyncKeyword
    case throwsKeyword
    case body
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawAccessorDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `AccessorDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `AccessorDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> AccessorDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifier: DeclModifierSyntax? {
    get {
      let childData = data.child(at: Cursor.modifier.rawValue)
      return childData.map { DeclModifierSyntax(data: $0) }
    }
    set(value) {
      self = withModifier(value)
    }
  }

  /// Returns a copy of the receiver with its `modifier` replaced.
  /// - param newChild: The new `modifier` to replace the node's
  ///                   current `modifier`, if present.
  public func withModifier(
    _ newChild: DeclModifierSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var accessorKind: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.accessorKind.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withAccessorKind(value)
    }
  }

  /// Returns a copy of the receiver with its `accessorKind` replaced.
  /// - param newChild: The new `accessorKind` to replace the node's
  ///                   current `accessorKind`, if present.
  public func withAccessorKind(
    _ newChild: TokenSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .unknown).raw

    let newRaw = raw.replacingChild(
      at: Cursor.accessorKind.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var parameter: AccessorParameterSyntax? {
    get {
      let childData = data.child(at: Cursor.parameter.rawValue)
      return childData.map { AccessorParameterSyntax(data: $0) }
    }
    set(value) {
      self = withParameter(value)
    }
  }

  /// Returns a copy of the receiver with its `parameter` replaced.
  /// - param newChild: The new `parameter` to replace the node's
  ///                   current `parameter`, if present.
  public func withParameter(
    _ newChild: AccessorParameterSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.parameter.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var asyncKeyword: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.asyncKeyword.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withAsyncKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `asyncKeyword` replaced.
  /// - param newChild: The new `asyncKeyword` to replace the node's
  ///                   current `asyncKeyword`, if present.
  public func withAsyncKeyword(
    _ newChild: TokenSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.asyncKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var throwsKeyword: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.throwsKeyword.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withThrowsKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `throwsKeyword` replaced.
  /// - param newChild: The new `throwsKeyword` to replace the node's
  ///                   current `throwsKeyword`, if present.
  public func withThrowsKeyword(
    _ newChild: TokenSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.throwsKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var body: CodeBlockSyntax? {
    get {
      let childData = data.child(at: Cursor.body.rawValue)
      return childData.map { CodeBlockSyntax(data: $0) }
    }
    set(value) {
      self = withBody(value)
    }
  }

  /// Returns a copy of the receiver with its `body` replaced.
  /// - param newChild: The new `body` to replace the node's
  ///                   current `body`, if present.
  public func withBody(
    _ newChild: CodeBlockSyntax?) -> AccessorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.body.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension AccessorDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifier": modifier.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "accessorKind": Syntax(accessorKind).asProtocol(SyntaxProtocol.self),
      "parameter": parameter.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "asyncKeyword": asyncKeyword.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "throwsKeyword": throwsKeyword.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "body": body.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - VariableDeclSyntax

public struct VariableDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case letOrVarKeyword
    case bindings
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawVariableDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `VariableDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `VariableDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> VariableDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> VariableDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> VariableDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> VariableDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var letOrVarKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.letOrVarKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLetOrVarKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `letOrVarKeyword` replaced.
  /// - param newChild: The new `letOrVarKeyword` to replace the node's
  ///                   current `letOrVarKeyword`, if present.
  public func withLetOrVarKeyword(
    _ newChild: TokenSyntax?) -> VariableDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .letKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.letOrVarKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var bindings: PatternBindingListSyntax {
    get {
      let childData = data.child(at: Cursor.bindings.rawValue)
      return PatternBindingListSyntax(data: childData!)
    }
    set(value) {
      self = withBindings(value)
    }
  }

  /// Adds the provided `Binding` to the node's `bindings`
  /// collection.
  /// - param element: The new `Binding` to add to the node's
  ///                  `bindings` collection.
  /// - returns: A copy of the receiver with the provided `Binding`
  ///            appended to its `bindings` collection.
  public func addBinding(_ element: PatternBindingSyntax) -> VariableDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.bindings.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .patternBindingList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.bindings.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `bindings` replaced.
  /// - param newChild: The new `bindings` to replace the node's
  ///                   current `bindings`, if present.
  public func withBindings(
    _ newChild: PatternBindingListSyntax?) -> VariableDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawPatternBindingListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.bindings.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension VariableDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "letOrVarKeyword": Syntax(letOrVarKeyword).asProtocol(SyntaxProtocol.self),
      "bindings": Syntax(bindings).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - EnumCaseDeclSyntax

/// 
/// A `case` declaration of a Swift `enum`. It can have 1 or more
/// `EnumCaseElement`s inside, each declaring a different case of the
/// enum.
/// 
public struct EnumCaseDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case caseKeyword
    case elements
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawEnumCaseDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `EnumCaseDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `EnumCaseDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  /// 
  /// The attributes applied to the case declaration.
  /// 
  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> EnumCaseDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> EnumCaseDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The declaration modifiers applied to the case declaration.
  /// 
  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> EnumCaseDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> EnumCaseDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// The `case` keyword for this case.
  public var caseKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.caseKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withCaseKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `caseKeyword` replaced.
  /// - param newChild: The new `caseKeyword` to replace the node's
  ///                   current `caseKeyword`, if present.
  public func withCaseKeyword(
    _ newChild: TokenSyntax?) -> EnumCaseDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .caseKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.caseKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// The elements this case declares.
  public var elements: EnumCaseElementListSyntax {
    get {
      let childData = data.child(at: Cursor.elements.rawValue)
      return EnumCaseElementListSyntax(data: childData!)
    }
    set(value) {
      self = withElements(value)
    }
  }

  /// Adds the provided `Element` to the node's `elements`
  /// collection.
  /// - param element: The new `Element` to add to the node's
  ///                  `elements` collection.
  /// - returns: A copy of the receiver with the provided `Element`
  ///            appended to its `elements` collection.
  public func addElement(_ element: EnumCaseElementSyntax) -> EnumCaseDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.elements.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .enumCaseElementList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.elements.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `elements` replaced.
  /// - param newChild: The new `elements` to replace the node's
  ///                   current `elements`, if present.
  public func withElements(
    _ newChild: EnumCaseElementListSyntax?) -> EnumCaseDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawEnumCaseElementListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.elements.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension EnumCaseDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "caseKeyword": Syntax(caseKeyword).asProtocol(SyntaxProtocol.self),
      "elements": Syntax(elements).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - EnumDeclSyntax

/// A Swift `enum` declaration.
public struct EnumDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case enumKeyword
    case identifier
    case genericParameters
    case inheritanceClause
    case genericWhereClause
    case members
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawEnumDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `EnumDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `EnumDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  /// 
  /// The attributes applied to the enum declaration.
  /// 
  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> EnumDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The declaration modifiers applied to the enum declaration.
  /// 
  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> EnumDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The `enum` keyword for this declaration.
  /// 
  public var enumKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.enumKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withEnumKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `enumKeyword` replaced.
  /// - param newChild: The new `enumKeyword` to replace the node's
  ///                   current `enumKeyword`, if present.
  public func withEnumKeyword(
    _ newChild: TokenSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .enumKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.enumKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The name of this enum.
  /// 
  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The generic parameters, if any, for this enum.
  /// 
  public var genericParameters: GenericParameterClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericParameters.rawValue)
      return childData.map { GenericParameterClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericParameters(value)
    }
  }

  /// Returns a copy of the receiver with its `genericParameters` replaced.
  /// - param newChild: The new `genericParameters` to replace the node's
  ///                   current `genericParameters`, if present.
  public func withGenericParameters(
    _ newChild: GenericParameterClauseSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericParameters.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The inheritance clause describing conformances or raw
  /// values for this enum.
  /// 
  public var inheritanceClause: TypeInheritanceClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.inheritanceClause.rawValue)
      return childData.map { TypeInheritanceClauseSyntax(data: $0) }
    }
    set(value) {
      self = withInheritanceClause(value)
    }
  }

  /// Returns a copy of the receiver with its `inheritanceClause` replaced.
  /// - param newChild: The new `inheritanceClause` to replace the node's
  ///                   current `inheritanceClause`, if present.
  public func withInheritanceClause(
    _ newChild: TypeInheritanceClauseSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.inheritanceClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The `where` clause that applies to the generic parameters of
  /// this enum.
  /// 
  public var genericWhereClause: GenericWhereClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericWhereClause.rawValue)
      return childData.map { GenericWhereClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericWhereClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericWhereClause` replaced.
  /// - param newChild: The new `genericWhereClause` to replace the node's
  ///                   current `genericWhereClause`, if present.
  public func withGenericWhereClause(
    _ newChild: GenericWhereClauseSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericWhereClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The cases and other members of this enum.
  /// 
  public var members: MemberDeclBlockSyntax {
    get {
      let childData = data.child(at: Cursor.members.rawValue)
      return MemberDeclBlockSyntax(data: childData!)
    }
    set(value) {
      self = withMembers(value)
    }
  }

  /// Returns a copy of the receiver with its `members` replaced.
  /// - param newChild: The new `members` to replace the node's
  ///                   current `members`, if present.
  public func withMembers(
    _ newChild: MemberDeclBlockSyntax?) -> EnumDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawMemberDeclBlockSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.members.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension EnumDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "enumKeyword": Syntax(enumKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "genericParameters": genericParameters.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "inheritanceClause": inheritanceClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "genericWhereClause": genericWhereClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "members": Syntax(members).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - OperatorDeclSyntax

/// A Swift `operator` declaration.
public struct OperatorDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case operatorKeyword
    case identifier
    case operatorPrecedenceAndTypes
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawOperatorDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `OperatorDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `OperatorDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  /// 
  /// The attributes applied to the 'operator' declaration.
  /// 
  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> OperatorDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> OperatorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The declaration modifiers applied to the 'operator'
  /// declaration.
  /// 
  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> OperatorDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> OperatorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var operatorKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.operatorKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withOperatorKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `operatorKeyword` replaced.
  /// - param newChild: The new `operatorKeyword` to replace the node's
  ///                   current `operatorKeyword`, if present.
  public func withOperatorKeyword(
    _ newChild: TokenSyntax?) -> OperatorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .operatorKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.operatorKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> OperatorDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .unspacedBinaryOperator).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// Optionally specify a precedence group and designated types.
  /// 
  public var operatorPrecedenceAndTypes: OperatorPrecedenceAndTypesSyntax? {
    get {
      let childData = data.child(at: Cursor.operatorPrecedenceAndTypes.rawValue)
      return childData.map { OperatorPrecedenceAndTypesSyntax(data: $0) }
    }
    set(value) {
      self = withOperatorPrecedenceAndTypes(value)
    }
  }

  /// Returns a copy of the receiver with its `operatorPrecedenceAndTypes` replaced.
  /// - param newChild: The new `operatorPrecedenceAndTypes` to replace the node's
  ///                   current `operatorPrecedenceAndTypes`, if present.
  public func withOperatorPrecedenceAndTypes(
    _ newChild: OperatorPrecedenceAndTypesSyntax?) -> OperatorDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.operatorPrecedenceAndTypes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension OperatorDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "operatorKeyword": Syntax(operatorKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "operatorPrecedenceAndTypes": operatorPrecedenceAndTypes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - PrecedenceGroupDeclSyntax

/// A Swift `precedencegroup` declaration.
public struct PrecedenceGroupDeclSyntax: DeclSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case attributes
    case modifiers
    case precedencegroupKeyword
    case identifier
    case leftBrace
    case groupAttributes
    case rightBrace
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawPrecedenceGroupDeclSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `PrecedenceGroupDeclSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `PrecedenceGroupDeclSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  /// 
  /// The attributes applied to the 'precedencegroup' declaration.
  /// 
  public var attributes: AttributeListSyntax? {
    get {
      let childData = data.child(at: Cursor.attributes.rawValue)
      return childData.map { AttributeListSyntax(data: $0) }
    }
    set(value) {
      self = withAttributes(value)
    }
  }

  /// Adds the provided `Attribute` to the node's `attributes`
  /// collection.
  /// - param element: The new `Attribute` to add to the node's
  ///                  `attributes` collection.
  /// - returns: A copy of the receiver with the provided `Attribute`
  ///            appended to its `attributes` collection.
  public func addAttribute(_ element: Syntax) -> PrecedenceGroupDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.attributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .attributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.attributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `attributes` replaced.
  /// - param newChild: The new `attributes` to replace the node's
  ///                   current `attributes`, if present.
  public func withAttributes(
    _ newChild: AttributeListSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The declaration modifiers applied to the 'precedencegroup'
  /// declaration.
  /// 
  public var modifiers: ModifierListSyntax? {
    get {
      let childData = data.child(at: Cursor.modifiers.rawValue)
      return childData.map { ModifierListSyntax(data: $0) }
    }
    set(value) {
      self = withModifiers(value)
    }
  }

  /// Adds the provided `Modifier` to the node's `modifiers`
  /// collection.
  /// - param element: The new `Modifier` to add to the node's
  ///                  `modifiers` collection.
  /// - returns: A copy of the receiver with the provided `Modifier`
  ///            appended to its `modifiers` collection.
  public func addModifier(_ element: DeclModifierSyntax) -> PrecedenceGroupDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.modifiers.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .modifierList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.modifiers.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `modifiers` replaced.
  /// - param newChild: The new `modifiers` to replace the node's
  ///                   current `modifiers`, if present.
  public func withModifiers(
    _ newChild: ModifierListSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.modifiers.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var precedencegroupKeyword: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.precedencegroupKeyword.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPrecedencegroupKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `precedencegroupKeyword` replaced.
  /// - param newChild: The new `precedencegroupKeyword` to replace the node's
  ///                   current `precedencegroupKeyword`, if present.
  public func withPrecedencegroupKeyword(
    _ newChild: TokenSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .precedencegroupKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.precedencegroupKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The name of this precedence group.
  /// 
  public var identifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.identifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withIdentifier(value)
    }
  }

  /// Returns a copy of the receiver with its `identifier` replaced.
  /// - param newChild: The new `identifier` to replace the node's
  ///                   current `identifier`, if present.
  public func withIdentifier(
    _ newChild: TokenSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.identifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var leftBrace: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftBrace.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftBrace(value)
    }
  }

  /// Returns a copy of the receiver with its `leftBrace` replaced.
  /// - param newChild: The new `leftBrace` to replace the node's
  ///                   current `leftBrace`, if present.
  public func withLeftBrace(
    _ newChild: TokenSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftBrace).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftBrace.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// 
  /// The characteristics of this precedence group.
  /// 
  public var groupAttributes: PrecedenceGroupAttributeListSyntax {
    get {
      let childData = data.child(at: Cursor.groupAttributes.rawValue)
      return PrecedenceGroupAttributeListSyntax(data: childData!)
    }
    set(value) {
      self = withGroupAttributes(value)
    }
  }

  /// Adds the provided `GroupAttribute` to the node's `groupAttributes`
  /// collection.
  /// - param element: The new `GroupAttribute` to add to the node's
  ///                  `groupAttributes` collection.
  /// - returns: A copy of the receiver with the provided `GroupAttribute`
  ///            appended to its `groupAttributes` collection.
  public func addGroupAttribute(_ element: Syntax) -> PrecedenceGroupDeclSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.groupAttributes.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .precedenceGroupAttributeList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.groupAttributes.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `groupAttributes` replaced.
  /// - param newChild: The new `groupAttributes` to replace the node's
  ///                   current `groupAttributes`, if present.
  public func withGroupAttributes(
    _ newChild: PrecedenceGroupAttributeListSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawPrecedenceGroupAttributeListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.groupAttributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightBrace: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightBrace.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightBrace(value)
    }
  }

  /// Returns a copy of the receiver with its `rightBrace` replaced.
  /// - param newChild: The new `rightBrace` to replace the node's
  ///                   current `rightBrace`, if present.
  public func withRightBrace(
    _ newChild: TokenSyntax?) -> PrecedenceGroupDeclSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightBrace).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightBrace.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension PrecedenceGroupDeclSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "modifiers": modifiers.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "precedencegroupKeyword": Syntax(precedencegroupKeyword).asProtocol(SyntaxProtocol.self),
      "identifier": Syntax(identifier).asProtocol(SyntaxProtocol.self),
      "leftBrace": Syntax(leftBrace).asProtocol(SyntaxProtocol.self),
      "groupAttributes": Syntax(groupAttributes).asProtocol(SyntaxProtocol.self),
      "rightBrace": Syntax(rightBrace).asProtocol(SyntaxProtocol.self),
    ])
  }
}
