@_spi(RawSyntax)
@frozen
public struct RawCanImportExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .canImportExpr
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
      _ unexpectedBeforeCanImportKeyword: RawUnexpectedNodesSyntax? = nil, 
      canImportKeyword: RawTokenSyntax, 
      _ unexpectedBetweenCanImportKeywordAndLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax, 
      _ unexpectedBetweenLeftParenAndImportPath: RawUnexpectedNodesSyntax? = nil, 
      importPath: RawTokenSyntax, 
      _ unexpectedBetweenImportPathAndVersionInfo: RawUnexpectedNodesSyntax? = nil, 
      versionInfo: RawCanImportVersionInfoSyntax?, 
      _ unexpectedBetweenVersionInfoAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .canImportExpr, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeCanImportKeyword?.raw
      layout[1] = canImportKeyword.raw
      layout[2] = unexpectedBetweenCanImportKeywordAndLeftParen?.raw
      layout[3] = leftParen.raw
      layout[4] = unexpectedBetweenLeftParenAndImportPath?.raw
      layout[5] = importPath.raw
      layout[6] = unexpectedBetweenImportPathAndVersionInfo?.raw
      layout[7] = versionInfo?.raw
      layout[8] = unexpectedBetweenVersionInfoAndRightParen?.raw
      layout[9] = rightParen.raw
      layout[10] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeCanImportKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var canImportKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCanImportKeywordAndLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftParenAndImportPath: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var importPath: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenImportPathAndVersionInfo: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var versionInfo: RawCanImportVersionInfoSyntax? {
    layoutView.children[7].map(RawCanImportVersionInfoSyntax.init(raw:))
  }
  
  public var unexpectedBetweenVersionInfoAndRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightParen: RawTokenSyntax {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCanImportVersionInfoSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .canImportVersionInfo
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
      _ unexpectedBeforeComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax, 
      _ unexpectedBetweenCommaAndLabel: RawUnexpectedNodesSyntax? = nil, 
      label: RawTokenSyntax, 
      _ unexpectedBetweenLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndVersion: RawUnexpectedNodesSyntax? = nil, 
      version: RawVersionTupleSyntax, 
      _ unexpectedAfterVersion: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .canImportVersionInfo, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeComma?.raw
      layout[1] = comma.raw
      layout[2] = unexpectedBetweenCommaAndLabel?.raw
      layout[3] = label.raw
      layout[4] = unexpectedBetweenLabelAndColon?.raw
      layout[5] = colon.raw
      layout[6] = unexpectedBetweenColonAndVersion?.raw
      layout[7] = version.raw
      layout[8] = unexpectedAfterVersion?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeComma: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCommaAndLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var label: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndVersion: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var version: RawVersionTupleSyntax {
    layoutView.children[7].map(RawVersionTupleSyntax.init(raw:))!
  }
  
  public var unexpectedAfterVersion: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCatchClauseListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .catchClauseList
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
  public init(elements: [RawCatchClauseSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .catchClauseList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawCatchClauseSyntax] {
    layoutView.children.map {
      RawCatchClauseSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCatchClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .catchClause
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
      _ unexpectedBeforeCatchKeyword: RawUnexpectedNodesSyntax? = nil, 
      catchKeyword: RawTokenSyntax, 
      _ unexpectedBetweenCatchKeywordAndCatchItems: RawUnexpectedNodesSyntax? = nil, 
      catchItems: RawCatchItemListSyntax, 
      _ unexpectedBetweenCatchItemsAndBody: RawUnexpectedNodesSyntax? = nil, 
      body: RawCodeBlockSyntax, 
      _ unexpectedAfterBody: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .catchClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeCatchKeyword?.raw
      layout[1] = catchKeyword.raw
      layout[2] = unexpectedBetweenCatchKeywordAndCatchItems?.raw
      layout[3] = catchItems.raw
      layout[4] = unexpectedBetweenCatchItemsAndBody?.raw
      layout[5] = body.raw
      layout[6] = unexpectedAfterBody?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeCatchKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var catchKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCatchKeywordAndCatchItems: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var catchItems: RawCatchItemListSyntax {
    layoutView.children[3].map(RawCatchItemListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCatchItemsAndBody: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var body: RawCodeBlockSyntax {
    layoutView.children[5].map(RawCodeBlockSyntax.init(raw:))!
  }
  
  public var unexpectedAfterBody: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCatchItemListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .catchItemList
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
  public init(elements: [RawCatchItemSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .catchItemList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawCatchItemSyntax] {
    layoutView.children.map {
      RawCatchItemSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCatchItemSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .catchItem
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
      pattern: RawPatternSyntax?, 
      _ unexpectedBetweenPatternAndWhereClause: RawUnexpectedNodesSyntax? = nil, 
      whereClause: RawWhereClauseSyntax?, 
      _ unexpectedBetweenWhereClauseAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .catchItem, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePattern?.raw
      layout[1] = pattern?.raw
      layout[2] = unexpectedBetweenPatternAndWhereClause?.raw
      layout[3] = whereClause?.raw
      layout[4] = unexpectedBetweenWhereClauseAndTrailingComma?.raw
      layout[5] = trailingComma?.raw
      layout[6] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePattern: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var pattern: RawPatternSyntax? {
    layoutView.children[1].map(RawPatternSyntax.init(raw:))
  }
  
  public var unexpectedBetweenPatternAndWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var whereClause: RawWhereClauseSyntax? {
    layoutView.children[3].map(RawWhereClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenWhereClauseAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClassDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .classDecl
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
      _ unexpectedBetweenModifiersAndClassKeyword: RawUnexpectedNodesSyntax? = nil, 
      classKeyword: RawTokenSyntax, 
      _ unexpectedBetweenClassKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
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
      kind: .classDecl, uninitializedCount: 17, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndClassKeyword?.raw
      layout[5] = classKeyword.raw
      layout[6] = unexpectedBetweenClassKeywordAndName?.raw
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
  
  public var unexpectedBetweenModifiersAndClassKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var classKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenClassKeywordAndName: RawUnexpectedNodesSyntax? {
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
public struct RawClassRestrictionTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .classRestrictionType
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
      _ unexpectedBeforeClassKeyword: RawUnexpectedNodesSyntax? = nil, 
      classKeyword: RawTokenSyntax, 
      _ unexpectedAfterClassKeyword: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .classRestrictionType, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeClassKeyword?.raw
      layout[1] = classKeyword.raw
      layout[2] = unexpectedAfterClassKeyword?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeClassKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var classKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterClassKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureCaptureClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureCaptureClause
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
      _ unexpectedBetweenLeftSquareAndItems: RawUnexpectedNodesSyntax? = nil, 
      items: RawClosureCaptureListSyntax, 
      _ unexpectedBetweenItemsAndRightSquare: RawUnexpectedNodesSyntax? = nil, 
      rightSquare: RawTokenSyntax, 
      _ unexpectedAfterRightSquare: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureCaptureClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftSquare?.raw
      layout[1] = leftSquare.raw
      layout[2] = unexpectedBetweenLeftSquareAndItems?.raw
      layout[3] = items.raw
      layout[4] = unexpectedBetweenItemsAndRightSquare?.raw
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
  
  public var unexpectedBetweenLeftSquareAndItems: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var items: RawClosureCaptureListSyntax {
    layoutView.children[3].map(RawClosureCaptureListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenItemsAndRightSquare: RawUnexpectedNodesSyntax? {
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
public struct RawClosureCaptureListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureCaptureList
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
  public init(elements: [RawClosureCaptureSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .closureCaptureList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawClosureCaptureSyntax] {
    layoutView.children.map {
      RawClosureCaptureSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureCaptureSpecifierSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureCaptureSpecifier
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
      specifier: RawTokenSyntax, 
      _ unexpectedBetweenSpecifierAndLeftParen: RawUnexpectedNodesSyntax? = nil, 
      leftParen: RawTokenSyntax?, 
      _ unexpectedBetweenLeftParenAndDetail: RawUnexpectedNodesSyntax? = nil, 
      detail: RawTokenSyntax?, 
      _ unexpectedBetweenDetailAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax?, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureCaptureSpecifier, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeSpecifier?.raw
      layout[1] = specifier.raw
      layout[2] = unexpectedBetweenSpecifierAndLeftParen?.raw
      layout[3] = leftParen?.raw
      layout[4] = unexpectedBetweenLeftParenAndDetail?.raw
      layout[5] = detail?.raw
      layout[6] = unexpectedBetweenDetailAndRightParen?.raw
      layout[7] = rightParen?.raw
      layout[8] = unexpectedAfterRightParen?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var specifier: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenSpecifierAndLeftParen: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftParen: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenLeftParenAndDetail: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var detail: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenDetailAndRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightParen: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterRightParen: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureCaptureSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureCapture
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
      specifier: RawClosureCaptureSpecifierSyntax?, 
      _ unexpectedBetweenSpecifierAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax?, 
      _ unexpectedBetweenNameAndEqual: RawUnexpectedNodesSyntax? = nil, 
      equal: RawTokenSyntax?, 
      _ unexpectedBetweenEqualAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedBetweenExpressionAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureCapture, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeSpecifier?.raw
      layout[1] = specifier?.raw
      layout[2] = unexpectedBetweenSpecifierAndName?.raw
      layout[3] = name?.raw
      layout[4] = unexpectedBetweenNameAndEqual?.raw
      layout[5] = equal?.raw
      layout[6] = unexpectedBetweenEqualAndExpression?.raw
      layout[7] = expression.raw
      layout[8] = unexpectedBetweenExpressionAndTrailingComma?.raw
      layout[9] = trailingComma?.raw
      layout[10] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var specifier: RawClosureCaptureSpecifierSyntax? {
    layoutView.children[1].map(RawClosureCaptureSpecifierSyntax.init(raw:))
  }
  
  public var unexpectedBetweenSpecifierAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenNameAndEqual: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var equal: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEqualAndExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[7].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawClosureExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureExpr
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
      _ unexpectedBetweenLeftBraceAndSignature: RawUnexpectedNodesSyntax? = nil, 
      signature: RawClosureSignatureSyntax?, 
      _ unexpectedBetweenSignatureAndStatements: RawUnexpectedNodesSyntax? = nil, 
      statements: RawCodeBlockItemListSyntax, 
      _ unexpectedBetweenStatementsAndRightBrace: RawUnexpectedNodesSyntax? = nil, 
      rightBrace: RawTokenSyntax, 
      _ unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureExpr, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftBrace?.raw
      layout[1] = leftBrace.raw
      layout[2] = unexpectedBetweenLeftBraceAndSignature?.raw
      layout[3] = signature?.raw
      layout[4] = unexpectedBetweenSignatureAndStatements?.raw
      layout[5] = statements.raw
      layout[6] = unexpectedBetweenStatementsAndRightBrace?.raw
      layout[7] = rightBrace.raw
      layout[8] = unexpectedAfterRightBrace?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftBrace: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftBraceAndSignature: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var signature: RawClosureSignatureSyntax? {
    layoutView.children[3].map(RawClosureSignatureSyntax.init(raw:))
  }
  
  public var unexpectedBetweenSignatureAndStatements: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var statements: RawCodeBlockItemListSyntax {
    layoutView.children[5].map(RawCodeBlockItemListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenStatementsAndRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightBrace: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureParameterClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureParameterClause
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
      _ unexpectedBetweenLeftParenAndParameters: RawUnexpectedNodesSyntax? = nil, 
      parameters: RawClosureParameterListSyntax, 
      _ unexpectedBetweenParametersAndRightParen: RawUnexpectedNodesSyntax? = nil, 
      rightParen: RawTokenSyntax, 
      _ unexpectedAfterRightParen: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureParameterClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftParen?.raw
      layout[1] = leftParen.raw
      layout[2] = unexpectedBetweenLeftParenAndParameters?.raw
      layout[3] = parameters.raw
      layout[4] = unexpectedBetweenParametersAndRightParen?.raw
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
  
  public var unexpectedBetweenLeftParenAndParameters: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var parameters: RawClosureParameterListSyntax {
    layoutView.children[3].map(RawClosureParameterListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenParametersAndRightParen: RawUnexpectedNodesSyntax? {
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
public struct RawClosureParameterListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureParameterList
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
  public init(elements: [RawClosureParameterSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .closureParameterList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawClosureParameterSyntax] {
    layoutView.children.map {
      RawClosureParameterSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureParameterSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureParameter
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
      _ unexpectedBetweenModifiersAndFirstName: RawUnexpectedNodesSyntax? = nil, 
      firstName: RawTokenSyntax, 
      _ unexpectedBetweenFirstNameAndSecondName: RawUnexpectedNodesSyntax? = nil, 
      secondName: RawTokenSyntax?, 
      _ unexpectedBetweenSecondNameAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax?, 
      _ unexpectedBetweenColonAndType: RawUnexpectedNodesSyntax? = nil, 
      type: RawTypeSyntax?, 
      _ unexpectedBetweenTypeAndEllipsis: RawUnexpectedNodesSyntax? = nil, 
      ellipsis: RawTokenSyntax?, 
      _ unexpectedBetweenEllipsisAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureParameter, uninitializedCount: 17, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndFirstName?.raw
      layout[5] = firstName.raw
      layout[6] = unexpectedBetweenFirstNameAndSecondName?.raw
      layout[7] = secondName?.raw
      layout[8] = unexpectedBetweenSecondNameAndColon?.raw
      layout[9] = colon?.raw
      layout[10] = unexpectedBetweenColonAndType?.raw
      layout[11] = type?.raw
      layout[12] = unexpectedBetweenTypeAndEllipsis?.raw
      layout[13] = ellipsis?.raw
      layout[14] = unexpectedBetweenEllipsisAndTrailingComma?.raw
      layout[15] = trailingComma?.raw
      layout[16] = unexpectedAfterTrailingComma?.raw
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
  
  public var unexpectedBetweenModifiersAndFirstName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var firstName: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenFirstNameAndSecondName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var secondName: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenSecondNameAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax? {
    layoutView.children[9].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenColonAndType: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax? {
    layoutView.children[11].map(RawTypeSyntax.init(raw:))
  }
  
  public var unexpectedBetweenTypeAndEllipsis: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var ellipsis: RawTokenSyntax? {
    layoutView.children[13].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEllipsisAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[15].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[16].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureShorthandParameterListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureShorthandParameterList
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
  public init(elements: [RawClosureShorthandParameterSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .closureShorthandParameterList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawClosureShorthandParameterSyntax] {
    layoutView.children.map {
      RawClosureShorthandParameterSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawClosureShorthandParameterSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .closureShorthandParameter
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
      kind: .closureShorthandParameter, uninitializedCount: 5, arena: arena) { layout in
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
public struct RawClosureSignatureSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum ParameterClause: RawSyntaxNodeProtocol {
    case `simpleInput`(RawClosureShorthandParameterListSyntax)
    case `parameterClause`(RawClosureParameterClauseSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawClosureShorthandParameterListSyntax.isKindOf(raw) || RawClosureParameterClauseSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .simpleInput(let node):
        return node.raw
      case .parameterClause(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawClosureShorthandParameterListSyntax(other) {
        self = .simpleInput(node)
        return
      }
      if let node = RawClosureParameterClauseSyntax(other) {
        self = .parameterClause(node)
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
    return raw.kind == .closureSignature
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
      _ unexpectedBetweenAttributesAndCapture: RawUnexpectedNodesSyntax? = nil, 
      capture: RawClosureCaptureClauseSyntax?, 
      _ unexpectedBetweenCaptureAndParameterClause: RawUnexpectedNodesSyntax? = nil, 
      parameterClause: ParameterClause?, 
      _ unexpectedBetweenParameterClauseAndEffectSpecifiers: RawUnexpectedNodesSyntax? = nil, 
      effectSpecifiers: RawTypeEffectSpecifiersSyntax?, 
      _ unexpectedBetweenEffectSpecifiersAndReturnClause: RawUnexpectedNodesSyntax? = nil, 
      returnClause: RawReturnClauseSyntax?, 
      _ unexpectedBetweenReturnClauseAndInKeyword: RawUnexpectedNodesSyntax? = nil, 
      inKeyword: RawTokenSyntax, 
      _ unexpectedAfterInKeyword: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .closureSignature, uninitializedCount: 13, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndCapture?.raw
      layout[3] = capture?.raw
      layout[4] = unexpectedBetweenCaptureAndParameterClause?.raw
      layout[5] = parameterClause?.raw
      layout[6] = unexpectedBetweenParameterClauseAndEffectSpecifiers?.raw
      layout[7] = effectSpecifiers?.raw
      layout[8] = unexpectedBetweenEffectSpecifiersAndReturnClause?.raw
      layout[9] = returnClause?.raw
      layout[10] = unexpectedBetweenReturnClauseAndInKeyword?.raw
      layout[11] = inKeyword.raw
      layout[12] = unexpectedAfterInKeyword?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[1].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndCapture: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var capture: RawClosureCaptureClauseSyntax? {
    layoutView.children[3].map(RawClosureCaptureClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenCaptureAndParameterClause: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var parameterClause: RawSyntax? {
    layoutView.children[5]
  }
  
  public var unexpectedBetweenParameterClauseAndEffectSpecifiers: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var effectSpecifiers: RawTypeEffectSpecifiersSyntax? {
    layoutView.children[7].map(RawTypeEffectSpecifiersSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEffectSpecifiersAndReturnClause: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var returnClause: RawReturnClauseSyntax? {
    layoutView.children[9].map(RawReturnClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenReturnClauseAndInKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var inKeyword: RawTokenSyntax {
    layoutView.children[11].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterInKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCodeBlockItemListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .codeBlockItemList
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
  public init(elements: [RawCodeBlockItemSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .codeBlockItemList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawCodeBlockItemSyntax] {
    layoutView.children.map {
      RawCodeBlockItemSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCodeBlockItemSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Item: RawSyntaxNodeProtocol {
    case `decl`(RawDeclSyntax)
    case `stmt`(RawStmtSyntax)
    case `expr`(RawExprSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawDeclSyntax.isKindOf(raw) || RawStmtSyntax.isKindOf(raw) || RawExprSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .decl(let node):
        return node.raw
      case .stmt(let node):
        return node.raw
      case .expr(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawDeclSyntax(other) {
        self = .decl(node)
        return
      }
      if let node = RawStmtSyntax(other) {
        self = .stmt(node)
        return
      }
      if let node = RawExprSyntax(other) {
        self = .expr(node)
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
    return raw.kind == .codeBlockItem
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
      _ unexpectedBeforeItem: RawUnexpectedNodesSyntax? = nil, 
      item: Item, 
      _ unexpectedBetweenItemAndSemicolon: RawUnexpectedNodesSyntax? = nil, 
      semicolon: RawTokenSyntax?, 
      _ unexpectedAfterSemicolon: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .codeBlockItem, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeItem?.raw
      layout[1] = item.raw
      layout[2] = unexpectedBetweenItemAndSemicolon?.raw
      layout[3] = semicolon?.raw
      layout[4] = unexpectedAfterSemicolon?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeItem: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var item: RawSyntax {
    layoutView.children[1]!
  }
  
  public var unexpectedBetweenItemAndSemicolon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var semicolon: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterSemicolon: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCodeBlockSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .codeBlock
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
      _ unexpectedBetweenLeftBraceAndStatements: RawUnexpectedNodesSyntax? = nil, 
      statements: RawCodeBlockItemListSyntax, 
      _ unexpectedBetweenStatementsAndRightBrace: RawUnexpectedNodesSyntax? = nil, 
      rightBrace: RawTokenSyntax, 
      _ unexpectedAfterRightBrace: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .codeBlock, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftBrace?.raw
      layout[1] = leftBrace.raw
      layout[2] = unexpectedBetweenLeftBraceAndStatements?.raw
      layout[3] = statements.raw
      layout[4] = unexpectedBetweenStatementsAndRightBrace?.raw
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
  
  public var unexpectedBetweenLeftBraceAndStatements: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var statements: RawCodeBlockItemListSyntax {
    layoutView.children[3].map(RawCodeBlockItemListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenStatementsAndRightBrace: RawUnexpectedNodesSyntax? {
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
public struct RawCompositionTypeElementListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .compositionTypeElementList
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
  public init(elements: [RawCompositionTypeElementSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .compositionTypeElementList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawCompositionTypeElementSyntax] {
    layoutView.children.map {
      RawCompositionTypeElementSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCompositionTypeElementSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .compositionTypeElement
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
      _ unexpectedBeforeType: RawUnexpectedNodesSyntax? = nil, 
      type: RawTypeSyntax, 
      _ unexpectedBetweenTypeAndAmpersand: RawUnexpectedNodesSyntax? = nil, 
      ampersand: RawTokenSyntax?, 
      _ unexpectedAfterAmpersand: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .compositionTypeElement, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeType?.raw
      layout[1] = type.raw
      layout[2] = unexpectedBetweenTypeAndAmpersand?.raw
      layout[3] = ampersand?.raw
      layout[4] = unexpectedAfterAmpersand?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenTypeAndAmpersand: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var ampersand: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterAmpersand: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCompositionTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .compositionType
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
      _ unexpectedBeforeElements: RawUnexpectedNodesSyntax? = nil, 
      elements: RawCompositionTypeElementListSyntax, 
      _ unexpectedAfterElements: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .compositionType, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeElements?.raw
      layout[1] = elements.raw
      layout[2] = unexpectedAfterElements?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeElements: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elements: RawCompositionTypeElementListSyntax {
    layoutView.children[1].map(RawCompositionTypeElementListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterElements: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawConditionElementListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .conditionElementList
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
  public init(elements: [RawConditionElementSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .conditionElementList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawConditionElementSyntax] {
    layoutView.children.map {
      RawConditionElementSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawConditionElementSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Condition: RawSyntaxNodeProtocol {
    case `expression`(RawExprSyntax)
    case `availability`(RawAvailabilityConditionSyntax)
    case `matchingPattern`(RawMatchingPatternConditionSyntax)
    case `optionalBinding`(RawOptionalBindingConditionSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawExprSyntax.isKindOf(raw) || RawAvailabilityConditionSyntax.isKindOf(raw) || RawMatchingPatternConditionSyntax.isKindOf(raw) || RawOptionalBindingConditionSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .expression(let node):
        return node.raw
      case .availability(let node):
        return node.raw
      case .matchingPattern(let node):
        return node.raw
      case .optionalBinding(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawExprSyntax(other) {
        self = .expression(node)
        return
      }
      if let node = RawAvailabilityConditionSyntax(other) {
        self = .availability(node)
        return
      }
      if let node = RawMatchingPatternConditionSyntax(other) {
        self = .matchingPattern(node)
        return
      }
      if let node = RawOptionalBindingConditionSyntax(other) {
        self = .optionalBinding(node)
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
    return raw.kind == .conditionElement
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
      _ unexpectedBeforeCondition: RawUnexpectedNodesSyntax? = nil, 
      condition: Condition, 
      _ unexpectedBetweenConditionAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .conditionElement, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeCondition?.raw
      layout[1] = condition.raw
      layout[2] = unexpectedBetweenConditionAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeCondition: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var condition: RawSyntax {
    layoutView.children[1]!
  }
  
  public var unexpectedBetweenConditionAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawConformanceRequirementSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .conformanceRequirement
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
      _ unexpectedBeforeLeftType: RawUnexpectedNodesSyntax? = nil, 
      leftType: RawTypeSyntax, 
      _ unexpectedBetweenLeftTypeAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndRightType: RawUnexpectedNodesSyntax? = nil, 
      rightType: RawTypeSyntax, 
      _ unexpectedAfterRightType: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .conformanceRequirement, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftType?.raw
      layout[1] = leftType.raw
      layout[2] = unexpectedBetweenLeftTypeAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndRightType?.raw
      layout[5] = rightType.raw
      layout[6] = unexpectedAfterRightType?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftType: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftTypeAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndRightType: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightType: RawTypeSyntax {
    layoutView.children[5].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightType: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawConsumeExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .consumeExpr
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
      _ unexpectedBeforeConsumeKeyword: RawUnexpectedNodesSyntax? = nil, 
      consumeKeyword: RawTokenSyntax, 
      _ unexpectedBetweenConsumeKeywordAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .consumeExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeConsumeKeyword?.raw
      layout[1] = consumeKeyword.raw
      layout[2] = unexpectedBetweenConsumeKeywordAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeConsumeKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var consumeKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenConsumeKeywordAndExpression: RawUnexpectedNodesSyntax? {
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
public struct RawContinueStmtSyntax: RawStmtSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .continueStmt
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
      _ unexpectedBeforeContinueKeyword: RawUnexpectedNodesSyntax? = nil, 
      continueKeyword: RawTokenSyntax, 
      _ unexpectedBetweenContinueKeywordAndLabel: RawUnexpectedNodesSyntax? = nil, 
      label: RawTokenSyntax?, 
      _ unexpectedAfterLabel: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .continueStmt, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeContinueKeyword?.raw
      layout[1] = continueKeyword.raw
      layout[2] = unexpectedBetweenContinueKeywordAndLabel?.raw
      layout[3] = label?.raw
      layout[4] = unexpectedAfterLabel?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeContinueKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var continueKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenContinueKeywordAndLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var label: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawConventionAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .conventionAttributeArguments
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
      _ unexpectedBeforeConventionLabel: RawUnexpectedNodesSyntax? = nil, 
      conventionLabel: RawTokenSyntax, 
      _ unexpectedBetweenConventionLabelAndComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax?, 
      _ unexpectedBetweenCommaAndCTypeLabel: RawUnexpectedNodesSyntax? = nil, 
      cTypeLabel: RawTokenSyntax?, 
      _ unexpectedBetweenCTypeLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax?, 
      _ unexpectedBetweenColonAndCTypeString: RawUnexpectedNodesSyntax? = nil, 
      cTypeString: RawStringLiteralExprSyntax?, 
      _ unexpectedAfterCTypeString: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .conventionAttributeArguments, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeConventionLabel?.raw
      layout[1] = conventionLabel.raw
      layout[2] = unexpectedBetweenConventionLabelAndComma?.raw
      layout[3] = comma?.raw
      layout[4] = unexpectedBetweenCommaAndCTypeLabel?.raw
      layout[5] = cTypeLabel?.raw
      layout[6] = unexpectedBetweenCTypeLabelAndColon?.raw
      layout[7] = colon?.raw
      layout[8] = unexpectedBetweenColonAndCTypeString?.raw
      layout[9] = cTypeString?.raw
      layout[10] = unexpectedAfterCTypeString?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeConventionLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var conventionLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenConventionLabelAndComma: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenCommaAndCTypeLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var cTypeLabel: RawTokenSyntax? {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenCTypeLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenColonAndCTypeString: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var cTypeString: RawStringLiteralExprSyntax? {
    layoutView.children[9].map(RawStringLiteralExprSyntax.init(raw:))
  }
  
  public var unexpectedAfterCTypeString: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawConventionWitnessMethodAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .conventionWitnessMethodAttributeArguments
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
      _ unexpectedBeforeWitnessMethodLabel: RawUnexpectedNodesSyntax? = nil, 
      witnessMethodLabel: RawTokenSyntax, 
      _ unexpectedBetweenWitnessMethodLabelAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax, 
      _ unexpectedBetweenColonAndProtocolName: RawUnexpectedNodesSyntax? = nil, 
      protocolName: RawTokenSyntax, 
      _ unexpectedAfterProtocolName: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .conventionWitnessMethodAttributeArguments, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeWitnessMethodLabel?.raw
      layout[1] = witnessMethodLabel.raw
      layout[2] = unexpectedBetweenWitnessMethodLabelAndColon?.raw
      layout[3] = colon.raw
      layout[4] = unexpectedBetweenColonAndProtocolName?.raw
      layout[5] = protocolName.raw
      layout[6] = unexpectedAfterProtocolName?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeWitnessMethodLabel: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var witnessMethodLabel: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenWitnessMethodLabelAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndProtocolName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var protocolName: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterProtocolName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawCopyExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .copyExpr
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
      _ unexpectedBeforeCopyKeyword: RawUnexpectedNodesSyntax? = nil, 
      copyKeyword: RawTokenSyntax, 
      _ unexpectedBetweenCopyKeywordAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .copyExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeCopyKeyword?.raw
      layout[1] = copyKeyword.raw
      layout[2] = unexpectedBetweenCopyKeywordAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeCopyKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var copyKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCopyKeywordAndExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}
