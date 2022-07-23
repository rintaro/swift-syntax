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



// MARK: - UnknownTypeSyntax

public struct UnknownTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawUnknownTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `UnknownTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `UnknownTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }
}

extension UnknownTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
    ])
  }
}

// MARK: - SimpleTypeIdentifierSyntax

public struct SimpleTypeIdentifierSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case name
    case genericArgumentClause
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawSimpleTypeIdentifierSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `SimpleTypeIdentifierSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `SimpleTypeIdentifierSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var name: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.name.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withName(value)
    }
  }

  /// Returns a copy of the receiver with its `name` replaced.
  /// - param newChild: The new `name` to replace the node's
  ///                   current `name`, if present.
  public func withName(
    _ newChild: TokenSyntax?) -> SimpleTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.name.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericArgumentClause: GenericArgumentClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericArgumentClause.rawValue)
      return childData.map { GenericArgumentClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericArgumentClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericArgumentClause` replaced.
  /// - param newChild: The new `genericArgumentClause` to replace the node's
  ///                   current `genericArgumentClause`, if present.
  public func withGenericArgumentClause(
    _ newChild: GenericArgumentClauseSyntax?) -> SimpleTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericArgumentClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension SimpleTypeIdentifierSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "name": Syntax(name).asProtocol(SyntaxProtocol.self),
      "genericArgumentClause": genericArgumentClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - MemberTypeIdentifierSyntax

public struct MemberTypeIdentifierSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case baseType
    case period
    case name
    case genericArgumentClause
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawMemberTypeIdentifierSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `MemberTypeIdentifierSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `MemberTypeIdentifierSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var baseType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.baseType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withBaseType(value)
    }
  }

  /// Returns a copy of the receiver with its `baseType` replaced.
  /// - param newChild: The new `baseType` to replace the node's
  ///                   current `baseType`, if present.
  public func withBaseType(
    _ newChild: TypeSyntax?) -> MemberTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.baseType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var period: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.period.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPeriod(value)
    }
  }

  /// Returns a copy of the receiver with its `period` replaced.
  /// - param newChild: The new `period` to replace the node's
  ///                   current `period`, if present.
  public func withPeriod(
    _ newChild: TokenSyntax?) -> MemberTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .period).raw

    let newRaw = raw.replacingChild(
      at: Cursor.period.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var name: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.name.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withName(value)
    }
  }

  /// Returns a copy of the receiver with its `name` replaced.
  /// - param newChild: The new `name` to replace the node's
  ///                   current `name`, if present.
  public func withName(
    _ newChild: TokenSyntax?) -> MemberTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.name.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var genericArgumentClause: GenericArgumentClauseSyntax? {
    get {
      let childData = data.child(at: Cursor.genericArgumentClause.rawValue)
      return childData.map { GenericArgumentClauseSyntax(data: $0) }
    }
    set(value) {
      self = withGenericArgumentClause(value)
    }
  }

  /// Returns a copy of the receiver with its `genericArgumentClause` replaced.
  /// - param newChild: The new `genericArgumentClause` to replace the node's
  ///                   current `genericArgumentClause`, if present.
  public func withGenericArgumentClause(
    _ newChild: GenericArgumentClauseSyntax?) -> MemberTypeIdentifierSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.genericArgumentClause.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension MemberTypeIdentifierSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "baseType": Syntax(baseType).asProtocol(SyntaxProtocol.self),
      "period": Syntax(period).asProtocol(SyntaxProtocol.self),
      "name": Syntax(name).asProtocol(SyntaxProtocol.self),
      "genericArgumentClause": genericArgumentClause.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
    ])
  }
}

// MARK: - ClassRestrictionTypeSyntax

public struct ClassRestrictionTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case classKeyword
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawClassRestrictionTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ClassRestrictionTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ClassRestrictionTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
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
    _ newChild: TokenSyntax?) -> ClassRestrictionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .classKeyword).raw

    let newRaw = raw.replacingChild(
      at: Cursor.classKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ClassRestrictionTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "classKeyword": Syntax(classKeyword).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ArrayTypeSyntax

public struct ArrayTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case leftSquareBracket
    case elementType
    case rightSquareBracket
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawArrayTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ArrayTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ArrayTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var leftSquareBracket: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftSquareBracket.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftSquareBracket(value)
    }
  }

  /// Returns a copy of the receiver with its `leftSquareBracket` replaced.
  /// - param newChild: The new `leftSquareBracket` to replace the node's
  ///                   current `leftSquareBracket`, if present.
  public func withLeftSquareBracket(
    _ newChild: TokenSyntax?) -> ArrayTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftSquareBracket).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftSquareBracket.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var elementType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.elementType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withElementType(value)
    }
  }

  /// Returns a copy of the receiver with its `elementType` replaced.
  /// - param newChild: The new `elementType` to replace the node's
  ///                   current `elementType`, if present.
  public func withElementType(
    _ newChild: TypeSyntax?) -> ArrayTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.elementType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightSquareBracket: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightSquareBracket.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightSquareBracket(value)
    }
  }

  /// Returns a copy of the receiver with its `rightSquareBracket` replaced.
  /// - param newChild: The new `rightSquareBracket` to replace the node's
  ///                   current `rightSquareBracket`, if present.
  public func withRightSquareBracket(
    _ newChild: TokenSyntax?) -> ArrayTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightSquareBracket).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightSquareBracket.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ArrayTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "leftSquareBracket": Syntax(leftSquareBracket).asProtocol(SyntaxProtocol.self),
      "elementType": Syntax(elementType).asProtocol(SyntaxProtocol.self),
      "rightSquareBracket": Syntax(rightSquareBracket).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - DictionaryTypeSyntax

public struct DictionaryTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case leftSquareBracket
    case keyType
    case colon
    case valueType
    case rightSquareBracket
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawDictionaryTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `DictionaryTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `DictionaryTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var leftSquareBracket: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.leftSquareBracket.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withLeftSquareBracket(value)
    }
  }

  /// Returns a copy of the receiver with its `leftSquareBracket` replaced.
  /// - param newChild: The new `leftSquareBracket` to replace the node's
  ///                   current `leftSquareBracket`, if present.
  public func withLeftSquareBracket(
    _ newChild: TokenSyntax?) -> DictionaryTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftSquareBracket).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftSquareBracket.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var keyType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.keyType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withKeyType(value)
    }
  }

  /// Returns a copy of the receiver with its `keyType` replaced.
  /// - param newChild: The new `keyType` to replace the node's
  ///                   current `keyType`, if present.
  public func withKeyType(
    _ newChild: TypeSyntax?) -> DictionaryTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.keyType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var colon: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.colon.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withColon(value)
    }
  }

  /// Returns a copy of the receiver with its `colon` replaced.
  /// - param newChild: The new `colon` to replace the node's
  ///                   current `colon`, if present.
  public func withColon(
    _ newChild: TokenSyntax?) -> DictionaryTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .colon).raw

    let newRaw = raw.replacingChild(
      at: Cursor.colon.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var valueType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.valueType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withValueType(value)
    }
  }

  /// Returns a copy of the receiver with its `valueType` replaced.
  /// - param newChild: The new `valueType` to replace the node's
  ///                   current `valueType`, if present.
  public func withValueType(
    _ newChild: TypeSyntax?) -> DictionaryTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.valueType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var rightSquareBracket: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.rightSquareBracket.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withRightSquareBracket(value)
    }
  }

  /// Returns a copy of the receiver with its `rightSquareBracket` replaced.
  /// - param newChild: The new `rightSquareBracket` to replace the node's
  ///                   current `rightSquareBracket`, if present.
  public func withRightSquareBracket(
    _ newChild: TokenSyntax?) -> DictionaryTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightSquareBracket).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightSquareBracket.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension DictionaryTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "leftSquareBracket": Syntax(leftSquareBracket).asProtocol(SyntaxProtocol.self),
      "keyType": Syntax(keyType).asProtocol(SyntaxProtocol.self),
      "colon": Syntax(colon).asProtocol(SyntaxProtocol.self),
      "valueType": Syntax(valueType).asProtocol(SyntaxProtocol.self),
      "rightSquareBracket": Syntax(rightSquareBracket).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - MetatypeTypeSyntax

public struct MetatypeTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case baseType
    case period
    case typeOrProtocol
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawMetatypeTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `MetatypeTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `MetatypeTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var baseType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.baseType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withBaseType(value)
    }
  }

  /// Returns a copy of the receiver with its `baseType` replaced.
  /// - param newChild: The new `baseType` to replace the node's
  ///                   current `baseType`, if present.
  public func withBaseType(
    _ newChild: TypeSyntax?) -> MetatypeTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.baseType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var period: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.period.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withPeriod(value)
    }
  }

  /// Returns a copy of the receiver with its `period` replaced.
  /// - param newChild: The new `period` to replace the node's
  ///                   current `period`, if present.
  public func withPeriod(
    _ newChild: TokenSyntax?) -> MetatypeTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .period).raw

    let newRaw = raw.replacingChild(
      at: Cursor.period.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var typeOrProtocol: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.typeOrProtocol.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withTypeOrProtocol(value)
    }
  }

  /// Returns a copy of the receiver with its `typeOrProtocol` replaced.
  /// - param newChild: The new `typeOrProtocol` to replace the node's
  ///                   current `typeOrProtocol`, if present.
  public func withTypeOrProtocol(
    _ newChild: TokenSyntax?) -> MetatypeTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.typeOrProtocol.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension MetatypeTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "baseType": Syntax(baseType).asProtocol(SyntaxProtocol.self),
      "period": Syntax(period).asProtocol(SyntaxProtocol.self),
      "typeOrProtocol": Syntax(typeOrProtocol).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - OptionalTypeSyntax

public struct OptionalTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case wrappedType
    case questionMark
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawOptionalTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `OptionalTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `OptionalTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var wrappedType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.wrappedType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withWrappedType(value)
    }
  }

  /// Returns a copy of the receiver with its `wrappedType` replaced.
  /// - param newChild: The new `wrappedType` to replace the node's
  ///                   current `wrappedType`, if present.
  public func withWrappedType(
    _ newChild: TypeSyntax?) -> OptionalTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.wrappedType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var questionMark: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.questionMark.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withQuestionMark(value)
    }
  }

  /// Returns a copy of the receiver with its `questionMark` replaced.
  /// - param newChild: The new `questionMark` to replace the node's
  ///                   current `questionMark`, if present.
  public func withQuestionMark(
    _ newChild: TokenSyntax?) -> OptionalTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .postfixQuestionMark).raw

    let newRaw = raw.replacingChild(
      at: Cursor.questionMark.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension OptionalTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "wrappedType": Syntax(wrappedType).asProtocol(SyntaxProtocol.self),
      "questionMark": Syntax(questionMark).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ConstrainedSugarTypeSyntax

public struct ConstrainedSugarTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case someOrAnySpecifier
    case baseType
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawConstrainedSugarTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ConstrainedSugarTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ConstrainedSugarTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var someOrAnySpecifier: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.someOrAnySpecifier.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withSomeOrAnySpecifier(value)
    }
  }

  /// Returns a copy of the receiver with its `someOrAnySpecifier` replaced.
  /// - param newChild: The new `someOrAnySpecifier` to replace the node's
  ///                   current `someOrAnySpecifier`, if present.
  public func withSomeOrAnySpecifier(
    _ newChild: TokenSyntax?) -> ConstrainedSugarTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .identifier).raw

    let newRaw = raw.replacingChild(
      at: Cursor.someOrAnySpecifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var baseType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.baseType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withBaseType(value)
    }
  }

  /// Returns a copy of the receiver with its `baseType` replaced.
  /// - param newChild: The new `baseType` to replace the node's
  ///                   current `baseType`, if present.
  public func withBaseType(
    _ newChild: TypeSyntax?) -> ConstrainedSugarTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.baseType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ConstrainedSugarTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "someOrAnySpecifier": Syntax(someOrAnySpecifier).asProtocol(SyntaxProtocol.self),
      "baseType": Syntax(baseType).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - ImplicitlyUnwrappedOptionalTypeSyntax

public struct ImplicitlyUnwrappedOptionalTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case wrappedType
    case exclamationMark
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawImplicitlyUnwrappedOptionalTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `ImplicitlyUnwrappedOptionalTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `ImplicitlyUnwrappedOptionalTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var wrappedType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.wrappedType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withWrappedType(value)
    }
  }

  /// Returns a copy of the receiver with its `wrappedType` replaced.
  /// - param newChild: The new `wrappedType` to replace the node's
  ///                   current `wrappedType`, if present.
  public func withWrappedType(
    _ newChild: TypeSyntax?) -> ImplicitlyUnwrappedOptionalTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.wrappedType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var exclamationMark: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.exclamationMark.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withExclamationMark(value)
    }
  }

  /// Returns a copy of the receiver with its `exclamationMark` replaced.
  /// - param newChild: The new `exclamationMark` to replace the node's
  ///                   current `exclamationMark`, if present.
  public func withExclamationMark(
    _ newChild: TokenSyntax?) -> ImplicitlyUnwrappedOptionalTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .exclamationMark).raw

    let newRaw = raw.replacingChild(
      at: Cursor.exclamationMark.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension ImplicitlyUnwrappedOptionalTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "wrappedType": Syntax(wrappedType).asProtocol(SyntaxProtocol.self),
      "exclamationMark": Syntax(exclamationMark).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - CompositionTypeSyntax

public struct CompositionTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case elements
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawCompositionTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `CompositionTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `CompositionTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var elements: CompositionTypeElementListSyntax {
    get {
      let childData = data.child(at: Cursor.elements.rawValue)
      return CompositionTypeElementListSyntax(data: childData!)
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
  public func addElement(_ element: CompositionTypeElementSyntax) -> CompositionTypeSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.elements.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .compositionTypeElementList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.elements.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `elements` replaced.
  /// - param newChild: The new `elements` to replace the node's
  ///                   current `elements`, if present.
  public func withElements(
    _ newChild: CompositionTypeElementListSyntax?) -> CompositionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawCompositionTypeElementListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.elements.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension CompositionTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "elements": Syntax(elements).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - TupleTypeSyntax

public struct TupleTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case leftParen
    case elements
    case rightParen
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawTupleTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `TupleTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `TupleTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
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
    _ newChild: TokenSyntax?) -> TupleTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var elements: TupleTypeElementListSyntax {
    get {
      let childData = data.child(at: Cursor.elements.rawValue)
      return TupleTypeElementListSyntax(data: childData!)
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
  public func addElement(_ element: TupleTypeElementSyntax) -> TupleTypeSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.elements.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .tupleTypeElementList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.elements.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `elements` replaced.
  /// - param newChild: The new `elements` to replace the node's
  ///                   current `elements`, if present.
  public func withElements(
    _ newChild: TupleTypeElementListSyntax?) -> TupleTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTupleTypeElementListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.elements.rawValue, with: newChildRaw, arena: arena)
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
    _ newChild: TokenSyntax?) -> TupleTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension TupleTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "leftParen": Syntax(leftParen).asProtocol(SyntaxProtocol.self),
      "elements": Syntax(elements).asProtocol(SyntaxProtocol.self),
      "rightParen": Syntax(rightParen).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - FunctionTypeSyntax

public struct FunctionTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case leftParen
    case arguments
    case rightParen
    case asyncKeyword
    case throwsOrRethrowsKeyword
    case arrow
    case returnType
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawFunctionTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `FunctionTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `FunctionTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
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
    _ newChild: TokenSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .leftParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.leftParen.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var arguments: TupleTypeElementListSyntax {
    get {
      let childData = data.child(at: Cursor.arguments.rawValue)
      return TupleTypeElementListSyntax(data: childData!)
    }
    set(value) {
      self = withArguments(value)
    }
  }

  /// Adds the provided `Argument` to the node's `arguments`
  /// collection.
  /// - param element: The new `Argument` to add to the node's
  ///                  `arguments` collection.
  /// - returns: A copy of the receiver with the provided `Argument`
  ///            appended to its `arguments` collection.
  public func addArgument(_ element: TupleTypeElementSyntax) -> FunctionTypeSyntax {
    var collection: RawSyntax
    if let col = raw.children[Cursor.arguments.rawValue] {
      collection = col.appending(element.raw, arena: self.arena)
    } else {
      collection = RawSyntax.makeLayout(arena: arena, kind: .tupleTypeElementList, from: [element.raw])
    }
    let newRaw = raw.replacingChild(at: Cursor.arguments.rawValue,
                                     with: collection, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  /// Returns a copy of the receiver with its `arguments` replaced.
  /// - param newChild: The new `arguments` to replace the node's
  ///                   current `arguments`, if present.
  public func withArguments(
    _ newChild: TupleTypeElementListSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTupleTypeElementListSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.arguments.rawValue, with: newChildRaw, arena: arena)
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
    _ newChild: TokenSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .rightParen).raw

    let newRaw = raw.replacingChild(
      at: Cursor.rightParen.rawValue, with: newChildRaw, arena: arena)
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
    _ newChild: TokenSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.asyncKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var throwsOrRethrowsKeyword: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.throwsOrRethrowsKeyword.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withThrowsOrRethrowsKeyword(value)
    }
  }

  /// Returns a copy of the receiver with its `throwsOrRethrowsKeyword` replaced.
  /// - param newChild: The new `throwsOrRethrowsKeyword` to replace the node's
  ///                   current `throwsOrRethrowsKeyword`, if present.
  public func withThrowsOrRethrowsKeyword(
    _ newChild: TokenSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.throwsOrRethrowsKeyword.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var arrow: TokenSyntax {
    get {
      let childData = data.child(at: Cursor.arrow.rawValue)
      return TokenSyntax(data: childData!)
    }
    set(value) {
      self = withArrow(value)
    }
  }

  /// Returns a copy of the receiver with its `arrow` replaced.
  /// - param newChild: The new `arrow` to replace the node's
  ///                   current `arrow`, if present.
  public func withArrow(
    _ newChild: TokenSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTokenSyntax.makeBlank(arena: arena, tokenKind: .arrow).raw

    let newRaw = raw.replacingChild(
      at: Cursor.arrow.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var returnType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.returnType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withReturnType(value)
    }
  }

  /// Returns a copy of the receiver with its `returnType` replaced.
  /// - param newChild: The new `returnType` to replace the node's
  ///                   current `returnType`, if present.
  public func withReturnType(
    _ newChild: TypeSyntax?) -> FunctionTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.returnType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension FunctionTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "leftParen": Syntax(leftParen).asProtocol(SyntaxProtocol.self),
      "arguments": Syntax(arguments).asProtocol(SyntaxProtocol.self),
      "rightParen": Syntax(rightParen).asProtocol(SyntaxProtocol.self),
      "asyncKeyword": asyncKeyword.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "throwsOrRethrowsKeyword": throwsOrRethrowsKeyword.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "arrow": Syntax(arrow).asProtocol(SyntaxProtocol.self),
      "returnType": Syntax(returnType).asProtocol(SyntaxProtocol.self),
    ])
  }
}

// MARK: - AttributedTypeSyntax

public struct AttributedTypeSyntax: TypeSyntaxProtocol, Hashable, Identifiable {
  public typealias ID = SyntaxIdentifier
  enum Cursor: Int {
    case specifier
    case attributes
    case baseType
  }

  public static func isValid(syntaxKind: SyntaxKind) -> Bool {
    RawAttributedTypeSyntax.isValid(syntaxKind: syntaxKind)
  }
  public let syntax: Syntax

  /// Converts the given `Syntax` node to a `AttributedTypeSyntax` if possible. Returns
  /// `nil` if the conversion is not possible.
  @inlinable
  public init?<Node: SyntaxProtocol>(_ other: Node) {
    guard Self.isValid(syntaxKind: other.syntax.syntaxKind) else { return nil }
    self.init(data: other.data)
  }

  /// Creates a `AttributedTypeSyntax` node from the given `SyntaxData`. This assumes
  /// that the `SyntaxData` is of the correct kind. If it is not, the behaviour
  /// is undefined.
  @usableFromInline
  internal init(data: SyntaxData) {
    assert(Self.isValid(syntaxKind: data.raw.syntaxKind))
    self.syntax = Syntax(data: data)
  }

  public var specifier: TokenSyntax? {
    get {
      let childData = data.child(at: Cursor.specifier.rawValue)
      return childData.map { TokenSyntax(data: $0) }
    }
    set(value) {
      self = withSpecifier(value)
    }
  }

  /// Returns a copy of the receiver with its `specifier` replaced.
  /// - param newChild: The new `specifier` to replace the node's
  ///                   current `specifier`, if present.
  public func withSpecifier(
    _ newChild: TokenSyntax?) -> AttributedTypeSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.specifier.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
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
  public func addAttribute(_ element: Syntax) -> AttributedTypeSyntax {
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
    _ newChild: AttributeListSyntax?) -> AttributedTypeSyntax {
    let newChildRaw = newChild?.raw

    let newRaw = raw.replacingChild(
      at: Cursor.attributes.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }

  public var baseType: TypeSyntax {
    get {
      let childData = data.child(at: Cursor.baseType.rawValue)
      return TypeSyntax(data: childData!)
    }
    set(value) {
      self = withBaseType(value)
    }
  }

  /// Returns a copy of the receiver with its `baseType` replaced.
  /// - param newChild: The new `baseType` to replace the node's
  ///                   current `baseType`, if present.
  public func withBaseType(
    _ newChild: TypeSyntax?) -> AttributedTypeSyntax {
    let newChildRaw = newChild?.raw
      ?? RawTypeSyntax.makeBlank(arena: arena).raw

    let newRaw = raw.replacingChild(
      at: Cursor.baseType.rawValue, with: newChildRaw, arena: arena)
    return Self(data: data.replacingSelf(with: newRaw, arena: arena))
  }
}

extension AttributedTypeSyntax: CustomReflectable {
  public var customMirror: Mirror {
    return Mirror(self, children: [
      "specifier": specifier.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "attributes": attributes.map(Syntax.init)?.asProtocol(SyntaxProtocol.self) as Any,
      "baseType": Syntax(baseType).asProtocol(SyntaxProtocol.self),
    ])
  }
}
