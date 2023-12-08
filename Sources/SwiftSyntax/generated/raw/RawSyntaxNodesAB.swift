@_spi(RawSyntax)
@frozen
public struct RawAccessorBlockSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Accessors: RawSyntaxNodeProtocol {
    case `accessors`(RawAccessorDeclListSyntax)
    case `getter`(RawCodeBlockItemListSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawAccessorDeclListSyntax.isKindOf(raw) || RawCodeBlockItemListSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .accessors(let node):
        return node.raw
      case .getter(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawAccessorDeclListSyntax(other) {
        self = .accessors(node)
        return
      }
      if let node = RawCodeBlockItemListSyntax(other) {
        self = .getter(node)
        return
      }
      return nil
    }
  }
  
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .accessorBlock
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLeftBrace: RawUnexpectedNodesSyntax? = nil, 
      leftBrace: RawTokenSyntax, 
      _ unexpectedBetweenLeftBraceAndAccessors: RawUnexpectedNodesSyntax? = nil, 
      accessors: Accessors, 
      _ unexpectedBetweenAccessorsAndRightBrace: RawUnexpectedNodesSyntax? = nil, 
      rightBrace: RawTokenSyntax, 
      _ unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .accessorBlock, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftBrace?.raw
      layout[1] = leftBrace.raw
      layout[2] = unexpectedBetweenLeftBraceAndAccessors?.raw
      layout[3] = accessors.raw
      layout[4] = unexpectedBetweenAccessorsAndRightBrace?.raw
      layout[5] = rightBrace.raw
      layout[6] = unexpectedAfterRightBrace?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftBrace: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftBraceAndAccessors: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var accessors: RawSyntax {
    layoutView.children[3]!
  }
  
  public var unexpectedBetweenAccessorsAndRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightBrace: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAccessorDeclListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .accessorDeclList
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  @inlinable
  public init(elements: [RawAccessorDeclSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .accessorDeclList, uninitializedCount: elements.count, arena: arena) { layout in
        guard var ptr = layout.baseAddress else {
          return
        }
        for elem in elements {
          ptr.initialize(to: elem.raw)
          ptr += 1
        }
    }
    self.init(unchecked: raw)
  }
  
  @inlinable
  public var elements: [RawAccessorDeclSyntax] {
    layoutView.children.map {
      RawAccessorDeclSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAccessorDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .accessorDecl
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? = nil, 
      attributes: RawAttributeListSyntax, 
      _ unexpectedBetweenAttributesAndModifier: RawUnexpectedNodesSyntax? = nil, 
      modifier: RawDeclModifierSyntax?, 
      _ unexpectedBetweenModifierAndAccessorSpecifier: RawUnexpectedNodesSyntax? = nil, 
      accessorSpecifier: RawTokenSyntax, 
      _ unexpectedBetweenAccessorSpecifierAndParameters: RawUnexpectedNodesSyntax? = nil, 
      parameters: RawAccessorParametersSyntax?, 
      _ unexpectedBetweenParametersAndEffectSpecifiers: RawUnexpectedNodesSyntax? = nil, 
      effectSpecifiers: RawAccessorEffectSpecifiersSyntax?, 
      _ unexpectedBetweenEffectSpecifiersAndBody: RawUnexpectedNodesSyntax? = nil, 
      body: RawCodeBlockSyntax?, 
      _ unexpectedAfterBody: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .accessorDecl, uninitializedCount: 13, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifier?.raw
      layout[3] = modifier?.raw
      layout[4] = unexpectedBetweenModifierAndAccessorSpecifier?.raw
      layout[5] = accessorSpecifier.raw
      layout[6] = unexpectedBetweenAccessorSpecifierAndParameters?.raw
      layout[7] = parameters?.raw
      layout[8] = unexpectedBetweenParametersAndEffectSpecifiers?.raw
      layout[9] = effectSpecifiers?.raw
      layout[10] = unexpectedBetweenEffectSpecifiersAndBody?.raw
      layout[11] = body?.raw
      layout[12] = unexpectedAfterBody?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[1].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndModifier: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var modifier: RawDeclModifierSyntax? {
    layoutView.children[3].map(RawDeclModifierSyntax.init(raw:))
  }
  
  public var unexpectedBetweenModifierAndAccessorSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var accessorSpecifier: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAccessorSpecifierAndParameters: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var parameters: RawAccessorParametersSyntax? {
    layoutView.children[7].map(RawAccessorParametersSyntax.init(raw:))
  }
  
  public var unexpectedBetweenParametersAndEffectSpecifiers: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var effectSpecifiers: RawAccessorEffectSpecifiersSyntax? {
    layoutView.children[9].map(RawAccessorEffectSpecifiersSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEffectSpecifiersAndBody: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var body: RawCodeBlockSyntax? {
    layoutView.children[11].map(RawCodeBlockSyntax.init(raw:))
  }
  
  public var unexpectedAfterBody: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAccessorEffectSpecifiersSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .accessorEffectSpecifiers
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAsyncSpecifier: RawUnexpectedNodesSyntax? = nil, 
      asyncSpecifier: RawTokenSyntax?, 
      _ unexpectedBetweenAsyncSpecifierAndThrowsClause: RawUnexpectedNodesSyntax? = nil, 
      throwsClause: RawThrowsClauseSyntax?, 
      _ unexpectedAfterThrowsClause: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .accessorEffectSpecifiers, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAsyncSpecifier?.raw
      layout[1] = asyncSpecifier?.raw
      layout[2] = unexpectedBetweenAsyncSpecifierAndThrowsClause?.raw
      layout[3] = throwsClause?.raw
      layout[4] = unexpectedAfterThrowsClause?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAsyncSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var asyncSpecifier: RawTokenSyntax? {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenAsyncSpecifierAndThrowsClause: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var throwsClause: RawThrowsClauseSyntax? {
    layoutView.children[3].map(RawThrowsClauseSyntax.init(raw:))
  }
  
  public var unexpectedAfterThrowsClause: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAccessorParametersSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .accessorParameters
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax, 
      _ unexpectedBetweenLeftParenAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .accessorParameters, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftParen?.raw
      layout[1] = leftParen.raw
      layout[2] = unexpectedBetweenLeftParenAndName?.raw
      layout[3] = name.raw
      layout[4] = unexpectedBetweenNameAndRightParen?.raw
      layout[5] = rightParen.raw
      layout[6] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftParenAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightParen: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawActorDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .actorDecl
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? = nil, 
      attributes: RawAttributeListSyntax, 
      _ unexpectedBetweenAttributesAndModifiers: RawUnexpectedNodesSyntax? = nil, 
      modifiers: RawDeclModifierListSyntax, 
      _ unexpectedBetweenModifiersAndActorKeyword: RawUnexpectedNodesSyntax? = nil, 
      actorKeyword: RawTokenSyntax, 
      _ unexpectedBetweenActorKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndGenericParameterClause: RawUnexpectedNodesSyntax? = nil, 
      genericParameterClause: RawGenericParameterClauseSyntax?, 
      _ unexpectedBetweenGenericParameterClauseAndInheritanceClause: RawUnexpectedNodesSyntax? = nil, 
      inheritanceClause: RawInheritanceClauseSyntax?, 
      _ unexpectedBetweenInheritanceClauseAndGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      genericWhereClause: RawGenericWhereClauseSyntax?, 
      _ unexpectedBetweenGenericWhereClauseAndMemberBlock: RawUnexpectedNodesSyntax? = nil, 
      memberBlock: RawMemberBlockSyntax, 
      _ unexpectedAfterMemberBlock: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .actorDecl, uninitializedCount: 17, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndActorKeyword?.raw
      layout[5] = actorKeyword.raw
      layout[6] = unexpectedBetweenActorKeywordAndName?.raw
      layout[7] = name.raw
      layout[8] = unexpectedBetweenNameAndGenericParameterClause?.raw
      layout[9] = genericParameterClause?.raw
      layout[10] = unexpectedBetweenGenericParameterClauseAndInheritanceClause?.raw
      layout[11] = inheritanceClause?.raw
      layout[12] = unexpectedBetweenInheritanceClauseAndGenericWhereClause?.raw
      layout[13] = genericWhereClause?.raw
      layout[14] = unexpectedBetweenGenericWhereClauseAndMemberBlock?.raw
      layout[15] = memberBlock.raw
      layout[16] = unexpectedAfterMemberBlock?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[1].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndModifiers: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var modifiers: RawDeclModifierListSyntax {
    layoutView.children[3].map(RawDeclModifierListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenModifiersAndActorKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var actorKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenActorKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndGenericParameterClause: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericParameterClause: RawGenericParameterClauseSyntax? {
    layoutView.children[9].map(RawGenericParameterClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenGenericParameterClauseAndInheritanceClause: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var inheritanceClause: RawInheritanceClauseSyntax? {
    layoutView.children[11].map(RawInheritanceClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenInheritanceClauseAndGenericWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericWhereClause: RawGenericWhereClauseSyntax? {
    layoutView.children[13].map(RawGenericWhereClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenGenericWhereClauseAndMemberBlock: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var memberBlock: RawMemberBlockSyntax {
    layoutView.children[15].map(RawMemberBlockSyntax.init(raw:))!
  }
  
  public var unexpectedAfterMemberBlock: RawUnexpectedNodesSyntax? {
    layoutView.children[16].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawArrayElementListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .arrayElementList
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  @inlinable
  public init(elements: [RawArrayElementSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .arrayElementList, uninitializedCount: elements.count, arena: arena) { layout in
        guard var ptr = layout.baseAddress else {
          return
        }
        for elem in elements {
          ptr.initialize(to: elem.raw)
          ptr += 1
        }
    }
    self.init(unchecked: raw)
  }
  
  @inlinable
  public var elements: [RawArrayElementSyntax] {
    layoutView.children.map {
      RawArrayElementSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawArrayElementSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .arrayElement
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedBetweenExpressionAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .arrayElement, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawArrayExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .arrayExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLeftSquare: RawUnexpectedNodesSyntax? = nil, 
      leftSquare: RawTokenSyntax, 
      _ unexpectedBetweenLeftSquareAndElements: RawUnexpectedNodesSyntax? = nil, 
      elements: RawArrayElementListSyntax, 
      _ unexpectedBetweenElementsAndRightSquare: RawUnexpectedNodesSyntax? = nil, 
      rightSquare: RawTokenSyntax, 
      _ unexpectedAfterRightSquare: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .arrayExpr, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftSquare?.raw
      layout[1] = leftSquare.raw
      layout[2] = unexpectedBetweenLeftSquareAndElements?.raw
      layout[3] = elements.raw
      layout[4] = unexpectedBetweenElementsAndRightSquare?.raw
      layout[5] = rightSquare.raw
      layout[6] = unexpectedAfterRightSquare?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftSquare: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftSquareAndElements: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elements: RawArrayElementListSyntax {
    layoutView.children[3].map(RawArrayElementListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenElementsAndRightSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightSquare: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawArrayTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .arrayType
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLeftSquare: RawUnexpectedNodesSyntax? = nil, 
      leftSquare: RawTokenSyntax, 
      _ unexpectedBetweenLeftSquareAndElement: RawUnexpectedNodesSyntax? = nil, 
      element: RawTypeSyntax, 
      _ unexpectedBetweenElementAndRightSquare: RawUnexpectedNodesSyntax? = nil, 
      rightSquare: RawTokenSyntax, 
      _ unexpectedAfterRightSquare: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .arrayType, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftSquare?.raw
      layout[1] = leftSquare.raw
      layout[2] = unexpectedBetweenLeftSquareAndElement?.raw
      layout[3] = element.raw
      layout[4] = unexpectedBetweenElementAndRightSquare?.raw
      layout[5] = rightSquare.raw
      layout[6] = unexpectedAfterRightSquare?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftSquare: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftSquareAndElement: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var element: RawTypeSyntax {
    layoutView.children[3].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenElementAndRightSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightSquare: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightSquare: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawArrowExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .arrowExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeEffectSpecifiers: RawUnexpectedNodesSyntax? = nil, 
      effectSpecifiers: RawTypeEffectSpecifiersSyntax?, 
      _ unexpectedBetweenEffectSpecifiersAndArrow: RawUnexpectedNodesSyntax? = nil, 
      arrow: RawTokenSyntax, 
      _ unexpectedAfterArrow: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .arrowExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeEffectSpecifiers?.raw
      layout[1] = effectSpecifiers?.raw
      layout[2] = unexpectedBetweenEffectSpecifiersAndArrow?.raw
      layout[3] = arrow.raw
      layout[4] = unexpectedAfterArrow?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeEffectSpecifiers: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var effectSpecifiers: RawTypeEffectSpecifiersSyntax? {
    layoutView.children[1].map(RawTypeEffectSpecifiersSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEffectSpecifiersAndArrow: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var arrow: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterArrow: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAsExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .asExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedBetweenExpressionAndAsKeyword: RawUnexpectedNodesSyntax? = nil, 
      asKeyword: RawTokenSyntax, 
      _ unexpectedBetweenAsKeywordAndQuestionOrExclamationMark: RawUnexpectedNodesSyntax? = nil, 
      questionOrExclamationMark: RawTokenSyntax?, 
      _ unexpectedBetweenQuestionOrExclamationMarkAndType: RawUnexpectedNodesSyntax? = nil, 
      type: RawTypeSyntax, 
      _ unexpectedAfterType: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .asExpr, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndAsKeyword?.raw
      layout[3] = asKeyword.raw
      layout[4] = unexpectedBetweenAsKeywordAndQuestionOrExclamationMark?.raw
      layout[5] = questionOrExclamationMark?.raw
      layout[6] = unexpectedBetweenQuestionOrExclamationMarkAndType?.raw
      layout[7] = type.raw
      layout[8] = unexpectedAfterType?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndAsKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var asKeyword: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAsKeywordAndQuestionOrExclamationMark: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var questionOrExclamationMark: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenQuestionOrExclamationMarkAndType: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[7].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterType: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAssignmentExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .assignmentExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeEqual: RawUnexpectedNodesSyntax? = nil, 
      equal: RawTokenSyntax, 
      _ unexpectedAfterEqual: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .assignmentExpr, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeEqual?.raw
      layout[1] = equal.raw
      layout[2] = unexpectedAfterEqual?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeEqual: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var equal: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterEqual: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAssociatedTypeDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .associatedTypeDecl
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? = nil, 
      attributes: RawAttributeListSyntax, 
      _ unexpectedBetweenAttributesAndModifiers: RawUnexpectedNodesSyntax? = nil, 
      modifiers: RawDeclModifierListSyntax, 
      _ unexpectedBetweenModifiersAndAssociatedtypeKeyword: RawUnexpectedNodesSyntax? = nil, 
      associatedtypeKeyword: RawTokenSyntax, 
      _ unexpectedBetweenAssociatedtypeKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndInheritanceClause: RawUnexpectedNodesSyntax? = nil, 
      inheritanceClause: RawInheritanceClauseSyntax?, 
      _ unexpectedBetweenInheritanceClauseAndInitializer: RawUnexpectedNodesSyntax? = nil, 
      initializer: RawTypeInitializerClauseSyntax?, 
      _ unexpectedBetweenInitializerAndGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      genericWhereClause: RawGenericWhereClauseSyntax?, 
      _ unexpectedAfterGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .associatedTypeDecl, uninitializedCount: 15, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndAssociatedtypeKeyword?.raw
      layout[5] = associatedtypeKeyword.raw
      layout[6] = unexpectedBetweenAssociatedtypeKeywordAndName?.raw
      layout[7] = name.raw
      layout[8] = unexpectedBetweenNameAndInheritanceClause?.raw
      layout[9] = inheritanceClause?.raw
      layout[10] = unexpectedBetweenInheritanceClauseAndInitializer?.raw
      layout[11] = initializer?.raw
      layout[12] = unexpectedBetweenInitializerAndGenericWhereClause?.raw
      layout[13] = genericWhereClause?.raw
      layout[14] = unexpectedAfterGenericWhereClause?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[1].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndModifiers: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var modifiers: RawDeclModifierListSyntax {
    layoutView.children[3].map(RawDeclModifierListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenModifiersAndAssociatedtypeKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var associatedtypeKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAssociatedtypeKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndInheritanceClause: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var inheritanceClause: RawInheritanceClauseSyntax? {
    layoutView.children[9].map(RawInheritanceClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenInheritanceClauseAndInitializer: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var initializer: RawTypeInitializerClauseSyntax? {
    layoutView.children[11].map(RawTypeInitializerClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenInitializerAndGenericWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericWhereClause: RawGenericWhereClauseSyntax? {
    layoutView.children[13].map(RawGenericWhereClauseSyntax.init(raw:))
  }
  
  public var unexpectedAfterGenericWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAttributeListSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Element: RawSyntaxNodeProtocol {
    case `attribute`(RawAttributeSyntax)
    case `ifConfigDecl`(RawIfConfigDeclSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawAttributeSyntax.isKindOf(raw) || RawIfConfigDeclSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .attribute(let node):
        return node.raw
      case .ifConfigDecl(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawAttributeSyntax(other) {
        self = .attribute(node)
        return
      }
      if let node = RawIfConfigDeclSyntax(other) {
        self = .ifConfigDecl(node)
        return
      }
      return nil
    }
  }
  
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .attributeList
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  @inlinable
  public init(elements: [Element], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .attributeList, uninitializedCount: elements.count, arena: arena) { layout in
        guard var ptr = layout.baseAddress else {
          return
        }
        for elem in elements {
          ptr.initialize(to: elem.raw)
          ptr += 1
        }
    }
    self.init(unchecked: raw)
  }
  
  @inlinable
  public var elements: [RawSyntax] {
    layoutView.children.map {
      RawSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAttributeSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Arguments: RawSyntaxNodeProtocol {
    case `argumentList`(RawLabeledExprListSyntax)
    case `token`(RawTokenSyntax)
    case `string`(RawStringLiteralExprSyntax)
    case `availability`(RawAvailabilityArgumentListSyntax)
    case `specializeArguments`(RawSpecializeAttributeArgumentListSyntax)
    case `objCName`(RawObjCSelectorPieceListSyntax)
    case `implementsArguments`(RawImplementsAttributeArgumentsSyntax)
    case `differentiableArguments`(RawDifferentiableAttributeArgumentsSyntax)
    case `derivativeRegistrationArguments`(RawDerivativeAttributeArgumentsSyntax)
    case `backDeployedArguments`(RawBackDeployedAttributeArgumentsSyntax)
    case `conventionArguments`(RawConventionAttributeArgumentsSyntax)
    case `conventionWitnessMethodArguments`(RawConventionWitnessMethodAttributeArgumentsSyntax)
    case `opaqueReturnTypeOfAttributeArguments`(RawOpaqueReturnTypeOfAttributeArgumentsSyntax)
    case `exposeAttributeArguments`(RawExposeAttributeArgumentsSyntax)
    case `originallyDefinedInArguments`(RawOriginallyDefinedInAttributeArgumentsSyntax)
    case `underscorePrivateAttributeArguments`(RawUnderscorePrivateAttributeArgumentsSyntax)
    case `dynamicReplacementArguments`(RawDynamicReplacementAttributeArgumentsSyntax)
    case `unavailableFromAsyncArguments`(RawUnavailableFromAsyncAttributeArgumentsSyntax)
    case `effectsArguments`(RawEffectsAttributeArgumentListSyntax)
    case `documentationArguments`(RawDocumentationAttributeArgumentListSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawLabeledExprListSyntax.isKindOf(raw) || RawTokenSyntax.isKindOf(raw) || RawStringLiteralExprSyntax.isKindOf(raw) || RawAvailabilityArgumentListSyntax.isKindOf(raw) || RawSpecializeAttributeArgumentListSyntax.isKindOf(raw) || RawObjCSelectorPieceListSyntax.isKindOf(raw) || RawImplementsAttributeArgumentsSyntax.isKindOf(raw) || RawDifferentiableAttributeArgumentsSyntax.isKindOf(raw) || RawDerivativeAttributeArgumentsSyntax.isKindOf(raw) || RawBackDeployedAttributeArgumentsSyntax.isKindOf(raw) || RawConventionAttributeArgumentsSyntax.isKindOf(raw) || RawConventionWitnessMethodAttributeArgumentsSyntax.isKindOf(raw) || RawOpaqueReturnTypeOfAttributeArgumentsSyntax.isKindOf(raw) || RawExposeAttributeArgumentsSyntax.isKindOf(raw) || RawOriginallyDefinedInAttributeArgumentsSyntax.isKindOf(raw) || RawUnderscorePrivateAttributeArgumentsSyntax.isKindOf(raw) || RawDynamicReplacementAttributeArgumentsSyntax.isKindOf(raw) || RawUnavailableFromAsyncAttributeArgumentsSyntax.isKindOf(raw) || RawEffectsAttributeArgumentListSyntax.isKindOf(raw) || RawDocumentationAttributeArgumentListSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .argumentList(let node):
        return node.raw
      case .token(let node):
        return node.raw
      case .string(let node):
        return node.raw
      case .availability(let node):
        return node.raw
      case .specializeArguments(let node):
        return node.raw
      case .objCName(let node):
        return node.raw
      case .implementsArguments(let node):
        return node.raw
      case .differentiableArguments(let node):
        return node.raw
      case .derivativeRegistrationArguments(let node):
        return node.raw
      case .backDeployedArguments(let node):
        return node.raw
      case .conventionArguments(let node):
        return node.raw
      case .conventionWitnessMethodArguments(let node):
        return node.raw
      case .opaqueReturnTypeOfAttributeArguments(let node):
        return node.raw
      case .exposeAttributeArguments(let node):
        return node.raw
      case .originallyDefinedInArguments(let node):
        return node.raw
      case .underscorePrivateAttributeArguments(let node):
        return node.raw
      case .dynamicReplacementArguments(let node):
        return node.raw
      case .unavailableFromAsyncArguments(let node):
        return node.raw
      case .effectsArguments(let node):
        return node.raw
      case .documentationArguments(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawLabeledExprListSyntax(other) {
        self = .argumentList(node)
        return
      }
      if let node = RawTokenSyntax(other) {
        self = .token(node)
        return
      }
      if let node = RawStringLiteralExprSyntax(other) {
        self = .string(node)
        return
      }
      if let node = RawAvailabilityArgumentListSyntax(other) {
        self = .availability(node)
        return
      }
      if let node = RawSpecializeAttributeArgumentListSyntax(other) {
        self = .specializeArguments(node)
        return
      }
      if let node = RawObjCSelectorPieceListSyntax(other) {
        self = .objCName(node)
        return
      }
      if let node = RawImplementsAttributeArgumentsSyntax(other) {
        self = .implementsArguments(node)
        return
      }
      if let node = RawDifferentiableAttributeArgumentsSyntax(other) {
        self = .differentiableArguments(node)
        return
      }
      if let node = RawDerivativeAttributeArgumentsSyntax(other) {
        self = .derivativeRegistrationArguments(node)
        return
      }
      if let node = RawBackDeployedAttributeArgumentsSyntax(other) {
        self = .backDeployedArguments(node)
        return
      }
      if let node = RawConventionAttributeArgumentsSyntax(other) {
        self = .conventionArguments(node)
        return
      }
      if let node = RawConventionWitnessMethodAttributeArgumentsSyntax(other) {
        self = .conventionWitnessMethodArguments(node)
        return
      }
      if let node = RawOpaqueReturnTypeOfAttributeArgumentsSyntax(other) {
        self = .opaqueReturnTypeOfAttributeArguments(node)
        return
      }
      if let node = RawExposeAttributeArgumentsSyntax(other) {
        self = .exposeAttributeArguments(node)
        return
      }
      if let node = RawOriginallyDefinedInAttributeArgumentsSyntax(other) {
        self = .originallyDefinedInArguments(node)
        return
      }
      if let node = RawUnderscorePrivateAttributeArgumentsSyntax(other) {
        self = .underscorePrivateAttributeArguments(node)
        return
      }
      if let node = RawDynamicReplacementAttributeArgumentsSyntax(other) {
        self = .dynamicReplacementArguments(node)
        return
      }
      if let node = RawUnavailableFromAsyncAttributeArgumentsSyntax(other) {
        self = .unavailableFromAsyncArguments(node)
        return
      }
      if let node = RawEffectsAttributeArgumentListSyntax(other) {
        self = .effectsArguments(node)
        return
      }
      if let node = RawDocumentationAttributeArgumentListSyntax(other) {
        self = .documentationArguments(node)
        return
      }
      return nil
    }
  }
  
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .attribute
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAtSign: RawUnexpectedNodesSyntax? = nil, 
      atSign: RawTokenSyntax, 
      _ unexpectedBetweenAtSignAndAttributeName: RawUnexpectedNodesSyntax? = nil, 
      attributeName: RawTypeSyntax, 
      _ unexpectedBetweenAttributeNameAndLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax?, 
      _ unexpectedBetweenLeftParenAndArguments: RawUnexpectedNodesSyntax? = nil, 
      arguments: Arguments?, 
      _ unexpectedBetweenArgumentsAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax?, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .attribute, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAtSign?.raw
      layout[1] = atSign.raw
      layout[2] = unexpectedBetweenAtSignAndAttributeName?.raw
      layout[3] = attributeName.raw
      layout[4] = unexpectedBetweenAttributeNameAndLeftParen?.raw
      layout[5] = leftParen?.raw
      layout[6] = unexpectedBetweenLeftParenAndArguments?.raw
      layout[7] = arguments?.raw
      layout[8] = unexpectedBetweenArgumentsAndRightParen?.raw
      layout[9] = rightParen?.raw
      layout[10] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAtSign: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var atSign: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAtSignAndAttributeName: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributeName: RawTypeSyntax {
    layoutView.children[3].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributeNameAndLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenLeftParenAndArguments: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var arguments: RawSyntax? {
    layoutView.children[7]
  }
  
  public var unexpectedBetweenArgumentsAndRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightParen: RawTokenSyntax? {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAttributedTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .attributedType
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeSpecifier: RawUnexpectedNodesSyntax? = nil, 
      specifier: RawTokenSyntax?, 
      _ unexpectedBetweenSpecifierAndAttributes: RawUnexpectedNodesSyntax? = nil, 
      attributes: RawAttributeListSyntax, 
      _ unexpectedBetweenAttributesAndBaseType: RawUnexpectedNodesSyntax? = nil, 
      baseType: RawTypeSyntax, 
      _ unexpectedAfterBaseType: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .attributedType, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeSpecifier?.raw
      layout[1] = specifier?.raw
      layout[2] = unexpectedBetweenSpecifierAndAttributes?.raw
      layout[3] = attributes.raw
      layout[4] = unexpectedBetweenAttributesAndBaseType?.raw
      layout[5] = baseType.raw
      layout[6] = unexpectedAfterBaseType?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var specifier: RawTokenSyntax? {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenSpecifierAndAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[3].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndBaseType: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var baseType: RawTypeSyntax {
    layoutView.children[5].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterBaseType: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAvailabilityArgumentListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .availabilityArgumentList
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  @inlinable
  public init(elements: [RawAvailabilityArgumentSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .availabilityArgumentList, uninitializedCount: elements.count, arena: arena) { layout in
        guard var ptr = layout.baseAddress else {
          return
        }
        for elem in elements {
          ptr.initialize(to: elem.raw)
          ptr += 1
        }
    }
    self.init(unchecked: raw)
  }
  
  @inlinable
  public var elements: [RawAvailabilityArgumentSyntax] {
    layoutView.children.map {
      RawAvailabilityArgumentSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAvailabilityArgumentSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Argument: RawSyntaxNodeProtocol {
    case `token`(RawTokenSyntax)
    case `availabilityVersionRestriction`(RawPlatformVersionSyntax)
    case `availabilityLabeledArgument`(RawAvailabilityLabeledArgumentSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawTokenSyntax.isKindOf(raw) || RawPlatformVersionSyntax.isKindOf(raw) || RawAvailabilityLabeledArgumentSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .token(let node):
        return node.raw
      case .availabilityVersionRestriction(let node):
        return node.raw
      case .availabilityLabeledArgument(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawTokenSyntax(other) {
        self = .token(node)
        return
      }
      if let node = RawPlatformVersionSyntax(other) {
        self = .availabilityVersionRestriction(node)
        return
      }
      if let node = RawAvailabilityLabeledArgumentSyntax(other) {
        self = .availabilityLabeledArgument(node)
        return
      }
      return nil
    }
  }
  
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .availabilityArgument
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeArgument: RawUnexpectedNodesSyntax? = nil, 
      argument: Argument, 
      _ unexpectedBetweenArgumentAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .availabilityArgument, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeArgument?.raw
      layout[1] = argument.raw
      layout[2] = unexpectedBetweenArgumentAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeArgument: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var argument: RawSyntax {
    layoutView.children[1]!
  }
  
  public var unexpectedBetweenArgumentAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAvailabilityConditionSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .availabilityCondition
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAvailabilityKeyword: RawUnexpectedNodesSyntax? = nil, 
      availabilityKeyword: RawTokenSyntax, 
      _ unexpectedBetweenAvailabilityKeywordAndLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax, 
      _ unexpectedBetweenLeftParenAndAvailabilityArguments: RawUnexpectedNodesSyntax? = nil, 
      availabilityArguments: RawAvailabilityArgumentListSyntax, 
      _ unexpectedBetweenAvailabilityArgumentsAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .availabilityCondition, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAvailabilityKeyword?.raw
      layout[1] = availabilityKeyword.raw
      layout[2] = unexpectedBetweenAvailabilityKeywordAndLeftParen?.raw
      layout[3] = leftParen.raw
      layout[4] = unexpectedBetweenLeftParenAndAvailabilityArguments?.raw
      layout[5] = availabilityArguments.raw
      layout[6] = unexpectedBetweenAvailabilityArgumentsAndRightParen?.raw
      layout[7] = rightParen.raw
      layout[8] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAvailabilityKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var availabilityKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAvailabilityKeywordAndLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftParenAndAvailabilityArguments: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var availabilityArguments: RawAvailabilityArgumentListSyntax {
    layoutView.children[5].map(RawAvailabilityArgumentListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAvailabilityArgumentsAndRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightParen: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAvailabilityLabeledArgumentSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Value: RawSyntaxNodeProtocol {
    case `string`(RawSimpleStringLiteralExprSyntax)
    case `version`(RawVersionTupleSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawSimpleStringLiteralExprSyntax.isKindOf(raw) || RawVersionTupleSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .string(let node):
        return node.raw
      case .version(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawSimpleStringLiteralExprSyntax(other) {
        self = .string(node)
        return
      }
      if let node = RawVersionTupleSyntax(other) {
        self = .version(node)
        return
      }
      return nil
    }
  }
  
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .availabilityLabeledArgument
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLabel: RawUnexpectedNodesSyntax? = nil, 
      label: RawTokenSyntax, 
      _ unexpectedBetweenLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? = nil, 
      value: Value, 
      _ unexpectedAfterValue: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .availabilityLabeledArgument, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLabel?.raw
      layout[1] = label.raw
      layout[2] = unexpectedBetweenLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndValue?.raw
      layout[5] = value.raw
      layout[6] = unexpectedAfterValue?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var label: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var value: RawSyntax {
    layoutView.children[5]!
  }
  
  public var unexpectedAfterValue: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawAwaitExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .awaitExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeAwaitKeyword: RawUnexpectedNodesSyntax? = nil, 
      awaitKeyword: RawTokenSyntax, 
      _ unexpectedBetweenAwaitKeywordAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .awaitExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAwaitKeyword?.raw
      layout[1] = awaitKeyword.raw
      layout[2] = unexpectedBetweenAwaitKeywordAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAwaitKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var awaitKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAwaitKeywordAndExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawBackDeployedAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .backDeployedAttributeArguments
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeBeforeLabel: RawUnexpectedNodesSyntax? = nil, 
      beforeLabel: RawTokenSyntax, 
      _ unexpectedBetweenBeforeLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndPlatforms: RawUnexpectedNodesSyntax? = nil, 
      platforms: RawPlatformVersionItemListSyntax, 
      _ unexpectedAfterPlatforms: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .backDeployedAttributeArguments, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeBeforeLabel?.raw
      layout[1] = beforeLabel.raw
      layout[2] = unexpectedBetweenBeforeLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndPlatforms?.raw
      layout[5] = platforms.raw
      layout[6] = unexpectedAfterPlatforms?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeBeforeLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var beforeLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenBeforeLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndPlatforms: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var platforms: RawPlatformVersionItemListSyntax {
    layoutView.children[5].map(RawPlatformVersionItemListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPlatforms: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawBinaryOperatorExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .binaryOperatorExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeOperator: RawUnexpectedNodesSyntax? = nil, 
      operator: RawTokenSyntax, 
      _ unexpectedAfterOperator: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .binaryOperatorExpr, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeOperator?.raw
      layout[1] = `operator`.raw
      layout[2] = unexpectedAfterOperator?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var `operator`: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawBooleanLiteralExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .booleanLiteralExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeLiteral: RawUnexpectedNodesSyntax? = nil, 
      literal: RawTokenSyntax, 
      _ unexpectedAfterLiteral: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .booleanLiteralExpr, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLiteral?.raw
      layout[1] = literal.raw
      layout[2] = unexpectedAfterLiteral?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLiteral: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var literal: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterLiteral: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawBorrowExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .borrowExpr
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeBorrowKeyword: RawUnexpectedNodesSyntax? = nil, 
      borrowKeyword: RawTokenSyntax, 
      _ unexpectedBetweenBorrowKeywordAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .borrowExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeBorrowKeyword?.raw
      layout[1] = borrowKeyword.raw
      layout[2] = unexpectedBetweenBorrowKeywordAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeBorrowKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var borrowKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenBorrowKeywordAndExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawBreakStmtSyntax: RawStmtSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .breakStmt
  }
  
  public var raw: RawSyntax
  
  @inlinable
  init(raw: RawSyntax) {
    precondition(Self.isKindOf(raw))
    self.raw = raw
  }
  
  @inlinable
  init(unchecked raw: RawSyntax) {
    self.raw = raw
  }
  
  @inlinable
  public init?(_ other: some RawSyntaxNodeProtocol) {
    guard Self.isKindOf(other.raw) else {
      return nil
    }
    self.init(unchecked: other.raw)
  }
  
  public init(
      _ unexpectedBeforeBreakKeyword: RawUnexpectedNodesSyntax? = nil, 
      breakKeyword: RawTokenSyntax, 
      _ unexpectedBetweenBreakKeywordAndLabel: RawUnexpectedNodesSyntax? = nil, 
      label: RawTokenSyntax?, 
      _ unexpectedAfterLabel: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .breakStmt, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeBreakKeyword?.raw
      layout[1] = breakKeyword.raw
      layout[2] = unexpectedBetweenBreakKeywordAndLabel?.raw
      layout[3] = label?.raw
      layout[4] = unexpectedAfterLabel?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeBreakKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var breakKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenBreakKeywordAndLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var label: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}
