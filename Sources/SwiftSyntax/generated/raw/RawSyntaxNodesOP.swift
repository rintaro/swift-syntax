@_spi(RawSyntax)
public protocol RawPatternSyntaxNodeProtocol: RawSyntaxNodeProtocol {}

@_spi(RawSyntax)
@frozen
public struct RawObjCSelectorPieceListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .objCSelectorPieceList
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
  public init(elements: [RawObjCSelectorPieceSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .objCSelectorPieceList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawObjCSelectorPieceSyntax] {
    layoutView.children.map {
      RawObjCSelectorPieceSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawObjCSelectorPieceSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .objCSelectorPiece
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
      _ unexpectedBeforeName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax?, 
      _ unexpectedBetweenNameAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax?, 
      _ unexpectedAfterColon: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .objCSelectorPiece, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeName?.raw
      layout[1] = name?.raw
      layout[2] = unexpectedBetweenNameAndColon?.raw
      layout[3] = colon?.raw
      layout[4] = unexpectedAfterColon?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax? {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenNameAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterColon: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOpaqueReturnTypeOfAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .opaqueReturnTypeOfAttributeArguments
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
      _ unexpectedBeforeMangledName: RawUnexpectedNodesSyntax? = nil, 
      mangledName: RawStringLiteralExprSyntax, 
      _ unexpectedBetweenMangledNameAndComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax, 
      _ unexpectedBetweenCommaAndOrdinal: RawUnexpectedNodesSyntax? = nil, 
      ordinal: RawTokenSyntax, 
      _ unexpectedAfterOrdinal: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .opaqueReturnTypeOfAttributeArguments, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeMangledName?.raw
      layout[1] = mangledName.raw
      layout[2] = unexpectedBetweenMangledNameAndComma?.raw
      layout[3] = comma.raw
      layout[4] = unexpectedBetweenCommaAndOrdinal?.raw
      layout[5] = ordinal.raw
      layout[6] = unexpectedAfterOrdinal?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeMangledName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var mangledName: RawStringLiteralExprSyntax {
    layoutView.children[1].map(RawStringLiteralExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenMangledNameAndComma: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCommaAndOrdinal: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var ordinal: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterOrdinal: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOperatorDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .operatorDecl
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
      _ unexpectedBeforeFixitySpecifier: RawUnexpectedNodesSyntax? = nil, 
      fixitySpecifier: RawTokenSyntax, 
      _ unexpectedBetweenFixitySpecifierAndOperatorKeyword: RawUnexpectedNodesSyntax? = nil, 
      operatorKeyword: RawTokenSyntax, 
      _ unexpectedBetweenOperatorKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndOperatorPrecedenceAndTypes: RawUnexpectedNodesSyntax? = nil, 
      operatorPrecedenceAndTypes: RawOperatorPrecedenceAndTypesSyntax?, 
      _ unexpectedAfterOperatorPrecedenceAndTypes: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .operatorDecl, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeFixitySpecifier?.raw
      layout[1] = fixitySpecifier.raw
      layout[2] = unexpectedBetweenFixitySpecifierAndOperatorKeyword?.raw
      layout[3] = operatorKeyword.raw
      layout[4] = unexpectedBetweenOperatorKeywordAndName?.raw
      layout[5] = name.raw
      layout[6] = unexpectedBetweenNameAndOperatorPrecedenceAndTypes?.raw
      layout[7] = operatorPrecedenceAndTypes?.raw
      layout[8] = unexpectedAfterOperatorPrecedenceAndTypes?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeFixitySpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var fixitySpecifier: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenFixitySpecifierAndOperatorKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var operatorKeyword: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenOperatorKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndOperatorPrecedenceAndTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var operatorPrecedenceAndTypes: RawOperatorPrecedenceAndTypesSyntax? {
    layoutView.children[7].map(RawOperatorPrecedenceAndTypesSyntax.init(raw:))
  }
  
  public var unexpectedAfterOperatorPrecedenceAndTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOperatorPrecedenceAndTypesSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .operatorPrecedenceAndTypes
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
      _ unexpectedBeforeColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndPrecedenceGroup: RawUnexpectedNodesSyntax? = nil, 
      precedenceGroup: RawTokenSyntax, 
      _ unexpectedBetweenPrecedenceGroupAndDesignatedTypes: RawUnexpectedNodesSyntax? = nil, 
      designatedTypes: RawDesignatedTypeListSyntax, 
      _ unexpectedAfterDesignatedTypes: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .operatorPrecedenceAndTypes, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeColon?.raw
      layout[1] = colon.raw
      layout[2] = unexpectedBetweenColonAndPrecedenceGroup?.raw
      layout[3] = precedenceGroup.raw
      layout[4] = unexpectedBetweenPrecedenceGroupAndDesignatedTypes?.raw
      layout[5] = designatedTypes.raw
      layout[6] = unexpectedAfterDesignatedTypes?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeColon: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndPrecedenceGroup: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var precedenceGroup: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPrecedenceGroupAndDesignatedTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var designatedTypes: RawDesignatedTypeListSyntax {
    layoutView.children[5].map(RawDesignatedTypeListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterDesignatedTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOptionalBindingConditionSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .optionalBindingCondition
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
      _ unexpectedBeforeBindingSpecifier: RawUnexpectedNodesSyntax? = nil, 
      bindingSpecifier: RawTokenSyntax, 
      _ unexpectedBetweenBindingSpecifierAndPattern: RawUnexpectedNodesSyntax? = nil, 
      pattern: RawPatternSyntax, 
      _ unexpectedBetweenPatternAndTypeAnnotation: RawUnexpectedNodesSyntax? = nil, 
      typeAnnotation: RawTypeAnnotationSyntax?, 
      _ unexpectedBetweenTypeAnnotationAndInitializer: RawUnexpectedNodesSyntax? = nil, 
      initializer: RawInitializerClauseSyntax?, 
      _ unexpectedAfterInitializer: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .optionalBindingCondition, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeBindingSpecifier?.raw
      layout[1] = bindingSpecifier.raw
      layout[2] = unexpectedBetweenBindingSpecifierAndPattern?.raw
      layout[3] = pattern.raw
      layout[4] = unexpectedBetweenPatternAndTypeAnnotation?.raw
      layout[5] = typeAnnotation?.raw
      layout[6] = unexpectedBetweenTypeAnnotationAndInitializer?.raw
      layout[7] = initializer?.raw
      layout[8] = unexpectedAfterInitializer?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeBindingSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var bindingSpecifier: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenBindingSpecifierAndPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pattern: RawPatternSyntax {
    layoutView.children[3].map(RawPatternSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPatternAndTypeAnnotation: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var typeAnnotation: RawTypeAnnotationSyntax? {
    layoutView.children[5].map(RawTypeAnnotationSyntax.init(raw:))
  }
  
  public var unexpectedBetweenTypeAnnotationAndInitializer: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var initializer: RawInitializerClauseSyntax? {
    layoutView.children[7].map(RawInitializerClauseSyntax.init(raw:))
  }
  
  public var unexpectedAfterInitializer: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOptionalChainingExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .optionalChainingExpr
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
      _ unexpectedBetweenExpressionAndQuestionMark: RawUnexpectedNodesSyntax? = nil, 
      questionMark: RawTokenSyntax, 
      _ unexpectedAfterQuestionMark: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .optionalChainingExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndQuestionMark?.raw
      layout[3] = questionMark.raw
      layout[4] = unexpectedAfterQuestionMark?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndQuestionMark: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var questionMark: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterQuestionMark: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOptionalTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .optionalType
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
      _ unexpectedBeforeWrappedType: RawUnexpectedNodesSyntax? = nil, 
      wrappedType: RawTypeSyntax, 
      _ unexpectedBetweenWrappedTypeAndQuestionMark: RawUnexpectedNodesSyntax? = nil, 
      questionMark: RawTokenSyntax, 
      _ unexpectedAfterQuestionMark: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .optionalType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeWrappedType?.raw
      layout[1] = wrappedType.raw
      layout[2] = unexpectedBetweenWrappedTypeAndQuestionMark?.raw
      layout[3] = questionMark.raw
      layout[4] = unexpectedAfterQuestionMark?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeWrappedType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var wrappedType: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenWrappedTypeAndQuestionMark: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var questionMark: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterQuestionMark: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawOriginallyDefinedInAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .originallyDefinedInAttributeArguments
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
      _ unexpectedBeforeModuleLabel: RawUnexpectedNodesSyntax? = nil, 
      moduleLabel: RawTokenSyntax, 
      _ unexpectedBetweenModuleLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndModuleName: RawUnexpectedNodesSyntax? = nil, 
      moduleName: RawStringLiteralExprSyntax, 
      _ unexpectedBetweenModuleNameAndComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax, 
      _ unexpectedBetweenCommaAndPlatforms: RawUnexpectedNodesSyntax? = nil, 
      platforms: RawPlatformVersionItemListSyntax, 
      _ unexpectedAfterPlatforms: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .originallyDefinedInAttributeArguments, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeModuleLabel?.raw
      layout[1] = moduleLabel.raw
      layout[2] = unexpectedBetweenModuleLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndModuleName?.raw
      layout[5] = moduleName.raw
      layout[6] = unexpectedBetweenModuleNameAndComma?.raw
      layout[7] = comma.raw
      layout[8] = unexpectedBetweenCommaAndPlatforms?.raw
      layout[9] = platforms.raw
      layout[10] = unexpectedAfterPlatforms?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeModuleLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var moduleLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenModuleLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndModuleName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var moduleName: RawStringLiteralExprSyntax {
    layoutView.children[5].map(RawStringLiteralExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenModuleNameAndComma: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCommaAndPlatforms: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var platforms: RawPlatformVersionItemListSyntax {
    layoutView.children[9].map(RawPlatformVersionItemListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPlatforms: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPackElementExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .packElementExpr
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
      _ unexpectedBeforeEachKeyword: RawUnexpectedNodesSyntax? = nil, 
      eachKeyword: RawTokenSyntax, 
      _ unexpectedBetweenEachKeywordAndPack: RawUnexpectedNodesSyntax? = nil, 
      pack: RawExprSyntax, 
      _ unexpectedAfterPack: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .packElementExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeEachKeyword?.raw
      layout[1] = eachKeyword.raw
      layout[2] = unexpectedBetweenEachKeywordAndPack?.raw
      layout[3] = pack.raw
      layout[4] = unexpectedAfterPack?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeEachKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var eachKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenEachKeywordAndPack: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pack: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPack: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPackElementTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .packElementType
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
      _ unexpectedBeforeEachKeyword: RawUnexpectedNodesSyntax? = nil, 
      eachKeyword: RawTokenSyntax, 
      _ unexpectedBetweenEachKeywordAndPack: RawUnexpectedNodesSyntax? = nil, 
      pack: RawTypeSyntax, 
      _ unexpectedAfterPack: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .packElementType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeEachKeyword?.raw
      layout[1] = eachKeyword.raw
      layout[2] = unexpectedBetweenEachKeywordAndPack?.raw
      layout[3] = pack.raw
      layout[4] = unexpectedAfterPack?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeEachKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var eachKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenEachKeywordAndPack: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pack: RawTypeSyntax {
    layoutView.children[3].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPack: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPackExpansionExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .packExpansionExpr
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
      _ unexpectedBeforeRepeatKeyword: RawUnexpectedNodesSyntax? = nil, 
      repeatKeyword: RawTokenSyntax, 
      _ unexpectedBetweenRepeatKeywordAndRepetitionPattern: RawUnexpectedNodesSyntax? = nil, 
      repetitionPattern: RawExprSyntax, 
      _ unexpectedAfterRepetitionPattern: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .packExpansionExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeRepeatKeyword?.raw
      layout[1] = repeatKeyword.raw
      layout[2] = unexpectedBetweenRepeatKeywordAndRepetitionPattern?.raw
      layout[3] = repetitionPattern.raw
      layout[4] = unexpectedAfterRepetitionPattern?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeRepeatKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var repeatKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenRepeatKeywordAndRepetitionPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var repetitionPattern: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRepetitionPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPackExpansionTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .packExpansionType
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
      _ unexpectedBeforeRepeatKeyword: RawUnexpectedNodesSyntax? = nil, 
      repeatKeyword: RawTokenSyntax, 
      _ unexpectedBetweenRepeatKeywordAndRepetitionPattern: RawUnexpectedNodesSyntax? = nil, 
      repetitionPattern: RawTypeSyntax, 
      _ unexpectedAfterRepetitionPattern: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .packExpansionType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeRepeatKeyword?.raw
      layout[1] = repeatKeyword.raw
      layout[2] = unexpectedBetweenRepeatKeywordAndRepetitionPattern?.raw
      layout[3] = repetitionPattern.raw
      layout[4] = unexpectedAfterRepetitionPattern?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeRepeatKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var repeatKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenRepeatKeywordAndRepetitionPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var repetitionPattern: RawTypeSyntax {
    layoutView.children[3].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRepetitionPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPatternBindingListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .patternBindingList
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
  public init(elements: [RawPatternBindingSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .patternBindingList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawPatternBindingSyntax] {
    layoutView.children.map {
      RawPatternBindingSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPatternBindingSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .patternBinding
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
      _ unexpectedBeforePattern: RawUnexpectedNodesSyntax? = nil, 
      pattern: RawPatternSyntax, 
      _ unexpectedBetweenPatternAndTypeAnnotation: RawUnexpectedNodesSyntax? = nil, 
      typeAnnotation: RawTypeAnnotationSyntax?, 
      _ unexpectedBetweenTypeAnnotationAndInitializer: RawUnexpectedNodesSyntax? = nil, 
      initializer: RawInitializerClauseSyntax?, 
      _ unexpectedBetweenInitializerAndAccessorBlock: RawUnexpectedNodesSyntax? = nil, 
      accessorBlock: RawAccessorBlockSyntax?, 
      _ unexpectedBetweenAccessorBlockAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .patternBinding, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePattern?.raw
      layout[1] = pattern.raw
      layout[2] = unexpectedBetweenPatternAndTypeAnnotation?.raw
      layout[3] = typeAnnotation?.raw
      layout[4] = unexpectedBetweenTypeAnnotationAndInitializer?.raw
      layout[5] = initializer?.raw
      layout[6] = unexpectedBetweenInitializerAndAccessorBlock?.raw
      layout[7] = accessorBlock?.raw
      layout[8] = unexpectedBetweenAccessorBlockAndTrailingComma?.raw
      layout[9] = trailingComma?.raw
      layout[10] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePattern: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pattern: RawPatternSyntax {
    layoutView.children[1].map(RawPatternSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPatternAndTypeAnnotation: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var typeAnnotation: RawTypeAnnotationSyntax? {
    layoutView.children[3].map(RawTypeAnnotationSyntax.init(raw:))
  }
  
  public var unexpectedBetweenTypeAnnotationAndInitializer: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var initializer: RawInitializerClauseSyntax? {
    layoutView.children[5].map(RawInitializerClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenInitializerAndAccessorBlock: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var accessorBlock: RawAccessorBlockSyntax? {
    layoutView.children[7].map(RawAccessorBlockSyntax.init(raw:))
  }
  
  public var unexpectedBetweenAccessorBlockAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPatternExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .patternExpr
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
      _ unexpectedBeforePattern: RawUnexpectedNodesSyntax? = nil, 
      pattern: RawPatternSyntax, 
      _ unexpectedAfterPattern: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .patternExpr, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePattern?.raw
      layout[1] = pattern.raw
      layout[2] = unexpectedAfterPattern?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePattern: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pattern: RawPatternSyntax {
    layoutView.children[1].map(RawPatternSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPattern: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPatternSyntax: RawPatternSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    switch raw.kind {
    case .expressionPattern, .identifierPattern, .isTypePattern, .missingPattern, .tuplePattern, .valueBindingPattern, .wildcardPattern:
      return true
    default:
      return false
    }
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
  public init(_ other: some RawPatternSyntaxNodeProtocol) {
    self.init(unchecked: other.raw)
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPlatformVersionItemListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .platformVersionItemList
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
  public init(elements: [RawPlatformVersionItemSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .platformVersionItemList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawPlatformVersionItemSyntax] {
    layoutView.children.map {
      RawPlatformVersionItemSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPlatformVersionItemSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .platformVersionItem
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
      _ unexpectedBeforePlatformVersion: RawUnexpectedNodesSyntax? = nil, 
      platformVersion: RawPlatformVersionSyntax, 
      _ unexpectedBetweenPlatformVersionAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .platformVersionItem, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePlatformVersion?.raw
      layout[1] = platformVersion.raw
      layout[2] = unexpectedBetweenPlatformVersionAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePlatformVersion: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var platformVersion: RawPlatformVersionSyntax {
    layoutView.children[1].map(RawPlatformVersionSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPlatformVersionAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawPlatformVersionSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .platformVersion
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
      _ unexpectedBeforePlatform: RawUnexpectedNodesSyntax? = nil, 
      platform: RawTokenSyntax, 
      _ unexpectedBetweenPlatformAndVersion: RawUnexpectedNodesSyntax? = nil, 
      version: RawVersionTupleSyntax?, 
      _ unexpectedAfterVersion: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .platformVersion, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePlatform?.raw
      layout[1] = platform.raw
      layout[2] = unexpectedBetweenPlatformAndVersion?.raw
      layout[3] = version?.raw
      layout[4] = unexpectedAfterVersion?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePlatform: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var platform: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPlatformAndVersion: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var version: RawVersionTupleSyntax? {
    layoutView.children[3].map(RawVersionTupleSyntax.init(raw:))
  }
  
  public var unexpectedAfterVersion: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPostfixIfConfigExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .postfixIfConfigExpr
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
      _ unexpectedBeforeBase: RawUnexpectedNodesSyntax? = nil, 
      base: RawExprSyntax?, 
      _ unexpectedBetweenBaseAndConfig: RawUnexpectedNodesSyntax? = nil, 
      config: RawIfConfigDeclSyntax, 
      _ unexpectedAfterConfig: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .postfixIfConfigExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeBase?.raw
      layout[1] = base?.raw
      layout[2] = unexpectedBetweenBaseAndConfig?.raw
      layout[3] = config.raw
      layout[4] = unexpectedAfterConfig?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeBase: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var base: RawExprSyntax? {
    layoutView.children[1].map(RawExprSyntax.init(raw:))
  }
  
  public var unexpectedBetweenBaseAndConfig: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var config: RawIfConfigDeclSyntax {
    layoutView.children[3].map(RawIfConfigDeclSyntax.init(raw:))!
  }
  
  public var unexpectedAfterConfig: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPostfixOperatorExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .postfixOperatorExpr
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
      _ unexpectedBetweenExpressionAndOperator: RawUnexpectedNodesSyntax? = nil, 
      operator: RawTokenSyntax, 
      _ unexpectedAfterOperator: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .postfixOperatorExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndOperator?.raw
      layout[3] = `operator`.raw
      layout[4] = unexpectedAfterOperator?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var `operator`: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPoundSourceLocationArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .poundSourceLocationArguments
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
      _ unexpectedBeforeFileLabel: RawUnexpectedNodesSyntax? = nil, 
      fileLabel: RawTokenSyntax, 
      _ unexpectedBetweenFileLabelAndFileColon: RawUnexpectedNodesSyntax? = nil, 
      fileColon: RawTokenSyntax, 
      _ unexpectedBetweenFileColonAndFileName: RawUnexpectedNodesSyntax? = nil, 
      fileName: RawSimpleStringLiteralExprSyntax, 
      _ unexpectedBetweenFileNameAndComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax, 
      _ unexpectedBetweenCommaAndLineLabel: RawUnexpectedNodesSyntax? = nil, 
      lineLabel: RawTokenSyntax, 
      _ unexpectedBetweenLineLabelAndLineColon: RawUnexpectedNodesSyntax? = nil, 
      lineColon: RawTokenSyntax, 
      _ unexpectedBetweenLineColonAndLineNumber: RawUnexpectedNodesSyntax? = nil, 
      lineNumber: RawTokenSyntax, 
      _ unexpectedAfterLineNumber: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .poundSourceLocationArguments, uninitializedCount: 15, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeFileLabel?.raw
      layout[1] = fileLabel.raw
      layout[2] = unexpectedBetweenFileLabelAndFileColon?.raw
      layout[3] = fileColon.raw
      layout[4] = unexpectedBetweenFileColonAndFileName?.raw
      layout[5] = fileName.raw
      layout[6] = unexpectedBetweenFileNameAndComma?.raw
      layout[7] = comma.raw
      layout[8] = unexpectedBetweenCommaAndLineLabel?.raw
      layout[9] = lineLabel.raw
      layout[10] = unexpectedBetweenLineLabelAndLineColon?.raw
      layout[11] = lineColon.raw
      layout[12] = unexpectedBetweenLineColonAndLineNumber?.raw
      layout[13] = lineNumber.raw
      layout[14] = unexpectedAfterLineNumber?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeFileLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var fileLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenFileLabelAndFileColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var fileColon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenFileColonAndFileName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var fileName: RawSimpleStringLiteralExprSyntax {
    layoutView.children[5].map(RawSimpleStringLiteralExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenFileNameAndComma: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCommaAndLineLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var lineLabel: RawTokenSyntax {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLineLabelAndLineColon: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var lineColon: RawTokenSyntax {
    layoutView.children[11].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLineColonAndLineNumber: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var lineNumber: RawTokenSyntax {
    layoutView.children[13].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterLineNumber: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPoundSourceLocationSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .poundSourceLocation
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
      _ unexpectedBeforePoundSourceLocation: RawUnexpectedNodesSyntax? = nil, 
      poundSourceLocation: RawTokenSyntax, 
      _ unexpectedBetweenPoundSourceLocationAndLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax, 
      _ unexpectedBetweenLeftParenAndArguments: RawUnexpectedNodesSyntax? = nil, 
      arguments: RawPoundSourceLocationArgumentsSyntax?, 
      _ unexpectedBetweenArgumentsAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .poundSourceLocation, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePoundSourceLocation?.raw
      layout[1] = poundSourceLocation.raw
      layout[2] = unexpectedBetweenPoundSourceLocationAndLeftParen?.raw
      layout[3] = leftParen.raw
      layout[4] = unexpectedBetweenLeftParenAndArguments?.raw
      layout[5] = arguments?.raw
      layout[6] = unexpectedBetweenArgumentsAndRightParen?.raw
      layout[7] = rightParen.raw
      layout[8] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePoundSourceLocation: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var poundSourceLocation: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPoundSourceLocationAndLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftParenAndArguments: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var arguments: RawPoundSourceLocationArgumentsSyntax? {
    layoutView.children[5].map(RawPoundSourceLocationArgumentsSyntax.init(raw:))
  }
  
  public var unexpectedBetweenArgumentsAndRightParen: RawUnexpectedNodesSyntax? {
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
public struct RawPrecedenceGroupAssignmentSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupAssignment
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
      _ unexpectedBeforeAssignmentLabel: RawUnexpectedNodesSyntax? = nil, 
      assignmentLabel: RawTokenSyntax, 
      _ unexpectedBetweenAssignmentLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? = nil, 
      value: RawTokenSyntax, 
      _ unexpectedAfterValue: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupAssignment, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAssignmentLabel?.raw
      layout[1] = assignmentLabel.raw
      layout[2] = unexpectedBetweenAssignmentLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndValue?.raw
      layout[5] = value.raw
      layout[6] = unexpectedAfterValue?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAssignmentLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var assignmentLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAssignmentLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var value: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterValue: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrecedenceGroupAssociativitySyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupAssociativity
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
      _ unexpectedBeforeAssociativityLabel: RawUnexpectedNodesSyntax? = nil, 
      associativityLabel: RawTokenSyntax, 
      _ unexpectedBetweenAssociativityLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? = nil, 
      value: RawTokenSyntax, 
      _ unexpectedAfterValue: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupAssociativity, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAssociativityLabel?.raw
      layout[1] = associativityLabel.raw
      layout[2] = unexpectedBetweenAssociativityLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndValue?.raw
      layout[5] = value.raw
      layout[6] = unexpectedAfterValue?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAssociativityLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var associativityLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAssociativityLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndValue: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var value: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterValue: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrecedenceGroupAttributeListSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Element: RawSyntaxNodeProtocol {
    case `precedenceGroupRelation`(RawPrecedenceGroupRelationSyntax)
    case `precedenceGroupAssignment`(RawPrecedenceGroupAssignmentSyntax)
    case `precedenceGroupAssociativity`(RawPrecedenceGroupAssociativitySyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawPrecedenceGroupRelationSyntax.isKindOf(raw) || RawPrecedenceGroupAssignmentSyntax.isKindOf(raw) || RawPrecedenceGroupAssociativitySyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .precedenceGroupRelation(let node):
        return node.raw
      case .precedenceGroupAssignment(let node):
        return node.raw
      case .precedenceGroupAssociativity(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawPrecedenceGroupRelationSyntax(other) {
        self = .precedenceGroupRelation(node)
        return
      }
      if let node = RawPrecedenceGroupAssignmentSyntax(other) {
        self = .precedenceGroupAssignment(node)
        return
      }
      if let node = RawPrecedenceGroupAssociativitySyntax(other) {
        self = .precedenceGroupAssociativity(node)
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
    return raw.kind == .precedenceGroupAttributeList
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
      kind: .precedenceGroupAttributeList, uninitializedCount: elements.count, arena: arena) { layout in
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
public struct RawPrecedenceGroupDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupDecl
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
      _ unexpectedBetweenModifiersAndPrecedencegroupKeyword: RawUnexpectedNodesSyntax? = nil, 
      precedencegroupKeyword: RawTokenSyntax, 
      _ unexpectedBetweenPrecedencegroupKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndLeftBrace: RawUnexpectedNodesSyntax? = nil, 
      leftBrace: RawTokenSyntax, 
      _ unexpectedBetweenLeftBraceAndGroupAttributes: RawUnexpectedNodesSyntax? = nil, 
      groupAttributes: RawPrecedenceGroupAttributeListSyntax, 
      _ unexpectedBetweenGroupAttributesAndRightBrace: RawUnexpectedNodesSyntax? = nil, 
      rightBrace: RawTokenSyntax, 
      _ unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupDecl, uninitializedCount: 15, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndPrecedencegroupKeyword?.raw
      layout[5] = precedencegroupKeyword.raw
      layout[6] = unexpectedBetweenPrecedencegroupKeywordAndName?.raw
      layout[7] = name.raw
      layout[8] = unexpectedBetweenNameAndLeftBrace?.raw
      layout[9] = leftBrace.raw
      layout[10] = unexpectedBetweenLeftBraceAndGroupAttributes?.raw
      layout[11] = groupAttributes.raw
      layout[12] = unexpectedBetweenGroupAttributesAndRightBrace?.raw
      layout[13] = rightBrace.raw
      layout[14] = unexpectedAfterRightBrace?.raw
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
  
  public var unexpectedBetweenModifiersAndPrecedencegroupKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var precedencegroupKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPrecedencegroupKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndLeftBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftBrace: RawTokenSyntax {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftBraceAndGroupAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var groupAttributes: RawPrecedenceGroupAttributeListSyntax {
    layoutView.children[11].map(RawPrecedenceGroupAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenGroupAttributesAndRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightBrace: RawTokenSyntax {
    layoutView.children[13].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrecedenceGroupNameListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupNameList
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
  public init(elements: [RawPrecedenceGroupNameSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupNameList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawPrecedenceGroupNameSyntax] {
    layoutView.children.map {
      RawPrecedenceGroupNameSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrecedenceGroupNameSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupName
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
      _ unexpectedBeforeName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupName, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeName?.raw
      layout[1] = name.raw
      layout[2] = unexpectedBetweenNameAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawPrecedenceGroupRelationSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .precedenceGroupRelation
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
      _ unexpectedBeforeHigherThanOrLowerThanLabel: RawUnexpectedNodesSyntax? = nil, 
      higherThanOrLowerThanLabel: RawTokenSyntax, 
      _ unexpectedBetweenHigherThanOrLowerThanLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndPrecedenceGroups: RawUnexpectedNodesSyntax? = nil, 
      precedenceGroups: RawPrecedenceGroupNameListSyntax, 
      _ unexpectedAfterPrecedenceGroups: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .precedenceGroupRelation, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeHigherThanOrLowerThanLabel?.raw
      layout[1] = higherThanOrLowerThanLabel.raw
      layout[2] = unexpectedBetweenHigherThanOrLowerThanLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndPrecedenceGroups?.raw
      layout[5] = precedenceGroups.raw
      layout[6] = unexpectedAfterPrecedenceGroups?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeHigherThanOrLowerThanLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var higherThanOrLowerThanLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenHigherThanOrLowerThanLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndPrecedenceGroups: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var precedenceGroups: RawPrecedenceGroupNameListSyntax {
    layoutView.children[5].map(RawPrecedenceGroupNameListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPrecedenceGroups: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrefixOperatorExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .prefixOperatorExpr
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
      _ unexpectedBetweenOperatorAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .prefixOperatorExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeOperator?.raw
      layout[1] = `operator`.raw
      layout[2] = unexpectedBetweenOperatorAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var `operator`: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenOperatorAndExpression: RawUnexpectedNodesSyntax? {
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
public struct RawPrimaryAssociatedTypeClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .primaryAssociatedTypeClause
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
      _ unexpectedBeforeLeftAngle: RawUnexpectedNodesSyntax? = nil, 
      leftAngle: RawTokenSyntax, 
      _ unexpectedBetweenLeftAngleAndPrimaryAssociatedTypes: RawUnexpectedNodesSyntax? = nil, 
      primaryAssociatedTypes: RawPrimaryAssociatedTypeListSyntax, 
      _ unexpectedBetweenPrimaryAssociatedTypesAndRightAngle: RawUnexpectedNodesSyntax? = nil, 
      rightAngle: RawTokenSyntax, 
      _ unexpectedAfterRightAngle: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .primaryAssociatedTypeClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftAngle?.raw
      layout[1] = leftAngle.raw
      layout[2] = unexpectedBetweenLeftAngleAndPrimaryAssociatedTypes?.raw
      layout[3] = primaryAssociatedTypes.raw
      layout[4] = unexpectedBetweenPrimaryAssociatedTypesAndRightAngle?.raw
      layout[5] = rightAngle.raw
      layout[6] = unexpectedAfterRightAngle?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftAngle: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftAngleAndPrimaryAssociatedTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var primaryAssociatedTypes: RawPrimaryAssociatedTypeListSyntax {
    layoutView.children[3].map(RawPrimaryAssociatedTypeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPrimaryAssociatedTypesAndRightAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightAngle: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrimaryAssociatedTypeListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .primaryAssociatedTypeList
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
  public init(elements: [RawPrimaryAssociatedTypeSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .primaryAssociatedTypeList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawPrimaryAssociatedTypeSyntax] {
    layoutView.children.map {
      RawPrimaryAssociatedTypeSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawPrimaryAssociatedTypeSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .primaryAssociatedType
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
      _ unexpectedBeforeName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .primaryAssociatedType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeName?.raw
      layout[1] = name.raw
      layout[2] = unexpectedBetweenNameAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawProtocolDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .protocolDecl
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
      _ unexpectedBetweenModifiersAndProtocolKeyword: RawUnexpectedNodesSyntax? = nil, 
      protocolKeyword: RawTokenSyntax, 
      _ unexpectedBetweenProtocolKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndPrimaryAssociatedTypeClause: RawUnexpectedNodesSyntax? = nil, 
      primaryAssociatedTypeClause: RawPrimaryAssociatedTypeClauseSyntax?, 
      _ unexpectedBetweenPrimaryAssociatedTypeClauseAndInheritanceClause: RawUnexpectedNodesSyntax? = nil, 
      inheritanceClause: RawInheritanceClauseSyntax?, 
      _ unexpectedBetweenInheritanceClauseAndGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      genericWhereClause: RawGenericWhereClauseSyntax?, 
      _ unexpectedBetweenGenericWhereClauseAndMemberBlock: RawUnexpectedNodesSyntax? = nil, 
      memberBlock: RawMemberBlockSyntax, 
      _ unexpectedAfterMemberBlock: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .protocolDecl, uninitializedCount: 17, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndProtocolKeyword?.raw
      layout[5] = protocolKeyword.raw
      layout[6] = unexpectedBetweenProtocolKeywordAndName?.raw
      layout[7] = name.raw
      layout[8] = unexpectedBetweenNameAndPrimaryAssociatedTypeClause?.raw
      layout[9] = primaryAssociatedTypeClause?.raw
      layout[10] = unexpectedBetweenPrimaryAssociatedTypeClauseAndInheritanceClause?.raw
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
  
  public var unexpectedBetweenModifiersAndProtocolKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var protocolKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenProtocolKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndPrimaryAssociatedTypeClause: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var primaryAssociatedTypeClause: RawPrimaryAssociatedTypeClauseSyntax? {
    layoutView.children[9].map(RawPrimaryAssociatedTypeClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenPrimaryAssociatedTypeClauseAndInheritanceClause: RawUnexpectedNodesSyntax? {
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
