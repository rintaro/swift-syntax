@_spi(RawSyntax)
@frozen
public struct RawGenericArgumentClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericArgumentClause
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
      _ unexpectedBetweenLeftAngleAndArguments: RawUnexpectedNodesSyntax? = nil, 
      arguments: RawGenericArgumentListSyntax, 
      _ unexpectedBetweenArgumentsAndRightAngle: RawUnexpectedNodesSyntax? = nil, 
      rightAngle: RawTokenSyntax, 
      _ unexpectedAfterRightAngle: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericArgumentClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftAngle?.raw
      layout[1] = leftAngle.raw
      layout[2] = unexpectedBetweenLeftAngleAndArguments?.raw
      layout[3] = arguments.raw
      layout[4] = unexpectedBetweenArgumentsAndRightAngle?.raw
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
  
  public var unexpectedBetweenLeftAngleAndArguments: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var arguments: RawGenericArgumentListSyntax {
    layoutView.children[3].map(RawGenericArgumentListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenArgumentsAndRightAngle: RawUnexpectedNodesSyntax? {
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
public struct RawGenericArgumentListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericArgumentList
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
  public init(elements: [RawGenericArgumentSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .genericArgumentList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawGenericArgumentSyntax] {
    layoutView.children.map {
      RawGenericArgumentSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericArgumentSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericArgument
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
      argument: RawTypeSyntax, 
      _ unexpectedBetweenArgumentAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericArgument, uninitializedCount: 5, arena: arena) { layout in
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
  
  public var argument: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
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
public struct RawGenericParameterClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericParameterClause
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
      _ unexpectedBetweenLeftAngleAndParameters: RawUnexpectedNodesSyntax? = nil, 
      parameters: RawGenericParameterListSyntax, 
      _ unexpectedBetweenParametersAndGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      genericWhereClause: RawGenericWhereClauseSyntax?, 
      _ unexpectedBetweenGenericWhereClauseAndRightAngle: RawUnexpectedNodesSyntax? = nil, 
      rightAngle: RawTokenSyntax, 
      _ unexpectedAfterRightAngle: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericParameterClause, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftAngle?.raw
      layout[1] = leftAngle.raw
      layout[2] = unexpectedBetweenLeftAngleAndParameters?.raw
      layout[3] = parameters.raw
      layout[4] = unexpectedBetweenParametersAndGenericWhereClause?.raw
      layout[5] = genericWhereClause?.raw
      layout[6] = unexpectedBetweenGenericWhereClauseAndRightAngle?.raw
      layout[7] = rightAngle.raw
      layout[8] = unexpectedAfterRightAngle?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftAngle: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftAngleAndParameters: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var parameters: RawGenericParameterListSyntax {
    layoutView.children[3].map(RawGenericParameterListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenParametersAndGenericWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericWhereClause: RawGenericWhereClauseSyntax? {
    layoutView.children[5].map(RawGenericWhereClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenGenericWhereClauseAndRightAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightAngle: RawTokenSyntax {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightAngle: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericParameterListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericParameterList
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
  public init(elements: [RawGenericParameterSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .genericParameterList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawGenericParameterSyntax] {
    layoutView.children.map {
      RawGenericParameterSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericParameterSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericParameter
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
      _ unexpectedBetweenAttributesAndEachKeyword: RawUnexpectedNodesSyntax? = nil, 
      eachKeyword: RawTokenSyntax?, 
      _ unexpectedBetweenEachKeywordAndName: RawUnexpectedNodesSyntax? = nil, 
      name: RawTokenSyntax, 
      _ unexpectedBetweenNameAndColon: RawUnexpectedNodesSyntax? = nil, 
      colon: RawTokenSyntax?, 
      _ unexpectedBetweenColonAndInheritedType: RawUnexpectedNodesSyntax? = nil, 
      inheritedType: RawTypeSyntax?, 
      _ unexpectedBetweenInheritedTypeAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericParameter, uninitializedCount: 13, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndEachKeyword?.raw
      layout[3] = eachKeyword?.raw
      layout[4] = unexpectedBetweenEachKeywordAndName?.raw
      layout[5] = name.raw
      layout[6] = unexpectedBetweenNameAndColon?.raw
      layout[7] = colon?.raw
      layout[8] = unexpectedBetweenColonAndInheritedType?.raw
      layout[9] = inheritedType?.raw
      layout[10] = unexpectedBetweenInheritedTypeAndTrailingComma?.raw
      layout[11] = trailingComma?.raw
      layout[12] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAttributes: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var attributes: RawAttributeListSyntax {
    layoutView.children[1].map(RawAttributeListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAttributesAndEachKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var eachKeyword: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenEachKeywordAndName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndColon: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenColonAndInheritedType: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var inheritedType: RawTypeSyntax? {
    layoutView.children[9].map(RawTypeSyntax.init(raw:))
  }
  
  public var unexpectedBetweenInheritedTypeAndTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingComma: RawTokenSyntax? {
    layoutView.children[11].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericRequirementListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericRequirementList
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
  public init(elements: [RawGenericRequirementSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .genericRequirementList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawGenericRequirementSyntax] {
    layoutView.children.map {
      RawGenericRequirementSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericRequirementSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Requirement: RawSyntaxNodeProtocol {
    case `sameTypeRequirement`(RawSameTypeRequirementSyntax)
    case `conformanceRequirement`(RawConformanceRequirementSyntax)
    case `layoutRequirement`(RawLayoutRequirementSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawSameTypeRequirementSyntax.isKindOf(raw) || RawConformanceRequirementSyntax.isKindOf(raw) || RawLayoutRequirementSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .sameTypeRequirement(let node):
        return node.raw
      case .conformanceRequirement(let node):
        return node.raw
      case .layoutRequirement(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawSameTypeRequirementSyntax(other) {
        self = .sameTypeRequirement(node)
        return
      }
      if let node = RawConformanceRequirementSyntax(other) {
        self = .conformanceRequirement(node)
        return
      }
      if let node = RawLayoutRequirementSyntax(other) {
        self = .layoutRequirement(node)
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
    return raw.kind == .genericRequirement
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
      _ unexpectedBeforeRequirement: RawUnexpectedNodesSyntax? = nil, 
      requirement: Requirement, 
      _ unexpectedBetweenRequirementAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericRequirement, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeRequirement?.raw
      layout[1] = requirement.raw
      layout[2] = unexpectedBetweenRequirementAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeRequirement: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var requirement: RawSyntax {
    layoutView.children[1]!
  }
  
  public var unexpectedBetweenRequirementAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawGenericSpecializationExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericSpecializationExpr
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
      _ unexpectedBetweenExpressionAndGenericArgumentClause: RawUnexpectedNodesSyntax? = nil, 
      genericArgumentClause: RawGenericArgumentClauseSyntax, 
      _ unexpectedAfterGenericArgumentClause: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericSpecializationExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndGenericArgumentClause?.raw
      layout[3] = genericArgumentClause.raw
      layout[4] = unexpectedAfterGenericArgumentClause?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndGenericArgumentClause: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericArgumentClause: RawGenericArgumentClauseSyntax {
    layoutView.children[3].map(RawGenericArgumentClauseSyntax.init(raw:))!
  }
  
  public var unexpectedAfterGenericArgumentClause: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGenericWhereClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .genericWhereClause
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
      _ unexpectedBeforeWhereKeyword: RawUnexpectedNodesSyntax? = nil, 
      whereKeyword: RawTokenSyntax, 
      _ unexpectedBetweenWhereKeywordAndRequirements: RawUnexpectedNodesSyntax? = nil, 
      requirements: RawGenericRequirementListSyntax, 
      _ unexpectedAfterRequirements: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .genericWhereClause, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeWhereKeyword?.raw
      layout[1] = whereKeyword.raw
      layout[2] = unexpectedBetweenWhereKeywordAndRequirements?.raw
      layout[3] = requirements.raw
      layout[4] = unexpectedAfterRequirements?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeWhereKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var whereKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenWhereKeywordAndRequirements: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var requirements: RawGenericRequirementListSyntax {
    layoutView.children[3].map(RawGenericRequirementListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRequirements: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawGuardStmtSyntax: RawStmtSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .guardStmt
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
      _ unexpectedBeforeGuardKeyword: RawUnexpectedNodesSyntax? = nil, 
      guardKeyword: RawTokenSyntax, 
      _ unexpectedBetweenGuardKeywordAndConditions: RawUnexpectedNodesSyntax? = nil, 
      conditions: RawConditionElementListSyntax, 
      _ unexpectedBetweenConditionsAndElseKeyword: RawUnexpectedNodesSyntax? = nil, 
      elseKeyword: RawTokenSyntax, 
      _ unexpectedBetweenElseKeywordAndBody: RawUnexpectedNodesSyntax? = nil, 
      body: RawCodeBlockSyntax, 
      _ unexpectedAfterBody: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .guardStmt, uninitializedCount: 9, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeGuardKeyword?.raw
      layout[1] = guardKeyword.raw
      layout[2] = unexpectedBetweenGuardKeywordAndConditions?.raw
      layout[3] = conditions.raw
      layout[4] = unexpectedBetweenConditionsAndElseKeyword?.raw
      layout[5] = elseKeyword.raw
      layout[6] = unexpectedBetweenElseKeywordAndBody?.raw
      layout[7] = body.raw
      layout[8] = unexpectedAfterBody?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeGuardKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var guardKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenGuardKeywordAndConditions: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var conditions: RawConditionElementListSyntax {
    layoutView.children[3].map(RawConditionElementListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenConditionsAndElseKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elseKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenElseKeywordAndBody: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var body: RawCodeBlockSyntax {
    layoutView.children[7].map(RawCodeBlockSyntax.init(raw:))!
  }
  
  public var unexpectedAfterBody: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIdentifierPatternSyntax: RawPatternSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .identifierPattern
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
      _ unexpectedBeforeIdentifier: RawUnexpectedNodesSyntax? = nil, 
      identifier: RawTokenSyntax, 
      _ unexpectedAfterIdentifier: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .identifierPattern, uninitializedCount: 3, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeIdentifier?.raw
      layout[1] = identifier.raw
      layout[2] = unexpectedAfterIdentifier?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeIdentifier: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var identifier: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterIdentifier: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIdentifierTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .identifierType
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
      _ unexpectedBetweenNameAndGenericArgumentClause: RawUnexpectedNodesSyntax? = nil, 
      genericArgumentClause: RawGenericArgumentClauseSyntax?, 
      _ unexpectedAfterGenericArgumentClause: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .identifierType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeName?.raw
      layout[1] = name.raw
      layout[2] = unexpectedBetweenNameAndGenericArgumentClause?.raw
      layout[3] = genericArgumentClause?.raw
      layout[4] = unexpectedAfterGenericArgumentClause?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndGenericArgumentClause: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericArgumentClause: RawGenericArgumentClauseSyntax? {
    layoutView.children[3].map(RawGenericArgumentClauseSyntax.init(raw:))
  }
  
  public var unexpectedAfterGenericArgumentClause: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIfConfigClauseListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .ifConfigClauseList
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
  public init(elements: [RawIfConfigClauseSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .ifConfigClauseList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawIfConfigClauseSyntax] {
    layoutView.children.map {
      RawIfConfigClauseSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIfConfigClauseSyntax: RawSyntaxNodeProtocol {
  @frozen
  public enum Elements: RawSyntaxNodeProtocol {
    case `statements`(RawCodeBlockItemListSyntax)
    case `switchCases`(RawSwitchCaseListSyntax)
    case `decls`(RawMemberBlockItemListSyntax)
    case `postfixExpression`(RawExprSyntax)
    case `attributes`(RawAttributeListSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawCodeBlockItemListSyntax.isKindOf(raw) || RawSwitchCaseListSyntax.isKindOf(raw) || RawMemberBlockItemListSyntax.isKindOf(raw) || RawExprSyntax.isKindOf(raw) || RawAttributeListSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .statements(let node):
        return node.raw
      case .switchCases(let node):
        return node.raw
      case .decls(let node):
        return node.raw
      case .postfixExpression(let node):
        return node.raw
      case .attributes(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawCodeBlockItemListSyntax(other) {
        self = .statements(node)
        return
      }
      if let node = RawSwitchCaseListSyntax(other) {
        self = .switchCases(node)
        return
      }
      if let node = RawMemberBlockItemListSyntax(other) {
        self = .decls(node)
        return
      }
      if let node = RawExprSyntax(other) {
        self = .postfixExpression(node)
        return
      }
      if let node = RawAttributeListSyntax(other) {
        self = .attributes(node)
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
    return raw.kind == .ifConfigClause
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
      _ unexpectedBeforePoundKeyword: RawUnexpectedNodesSyntax? = nil, 
      poundKeyword: RawTokenSyntax, 
      _ unexpectedBetweenPoundKeywordAndCondition: RawUnexpectedNodesSyntax? = nil, 
      condition: RawExprSyntax?, 
      _ unexpectedBetweenConditionAndElements: RawUnexpectedNodesSyntax? = nil, 
      elements: Elements?, 
      _ unexpectedAfterElements: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .ifConfigClause, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforePoundKeyword?.raw
      layout[1] = poundKeyword.raw
      layout[2] = unexpectedBetweenPoundKeywordAndCondition?.raw
      layout[3] = condition?.raw
      layout[4] = unexpectedBetweenConditionAndElements?.raw
      layout[5] = elements?.raw
      layout[6] = unexpectedAfterElements?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforePoundKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var poundKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenPoundKeywordAndCondition: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var condition: RawExprSyntax? {
    layoutView.children[3].map(RawExprSyntax.init(raw:))
  }
  
  public var unexpectedBetweenConditionAndElements: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elements: RawSyntax? {
    layoutView.children[5]
  }
  
  public var unexpectedAfterElements: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIfConfigDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .ifConfigDecl
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
      _ unexpectedBeforeClauses: RawUnexpectedNodesSyntax? = nil, 
      clauses: RawIfConfigClauseListSyntax, 
      _ unexpectedBetweenClausesAndPoundEndif: RawUnexpectedNodesSyntax? = nil, 
      poundEndif: RawTokenSyntax, 
      _ unexpectedAfterPoundEndif: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .ifConfigDecl, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeClauses?.raw
      layout[1] = clauses.raw
      layout[2] = unexpectedBetweenClausesAndPoundEndif?.raw
      layout[3] = poundEndif.raw
      layout[4] = unexpectedAfterPoundEndif?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeClauses: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var clauses: RawIfConfigClauseListSyntax {
    layoutView.children[1].map(RawIfConfigClauseListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenClausesAndPoundEndif: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var poundEndif: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPoundEndif: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIfExprSyntax: RawExprSyntaxNodeProtocol {
  @frozen
  public enum ElseBody: RawSyntaxNodeProtocol {
    case `ifExpr`(RawIfExprSyntax)
    case `codeBlock`(RawCodeBlockSyntax)
    
    @inlinable
    public static func isKindOf(_ raw: RawSyntax) -> Bool {
      return RawIfExprSyntax.isKindOf(raw) || RawCodeBlockSyntax.isKindOf(raw)
    }
    
    @inlinable public var raw: RawSyntax {
      switch self {
      case .ifExpr(let node):
        return node.raw
      case .codeBlock(let node):
        return node.raw
      }
    }
    
    @inlinable public init?(_ other: some RawSyntaxNodeProtocol) {
      if let node = RawIfExprSyntax(other) {
        self = .ifExpr(node)
        return
      }
      if let node = RawCodeBlockSyntax(other) {
        self = .codeBlock(node)
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
    return raw.kind == .ifExpr
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
      _ unexpectedBeforeIfKeyword: RawUnexpectedNodesSyntax? = nil, 
      ifKeyword: RawTokenSyntax, 
      _ unexpectedBetweenIfKeywordAndConditions: RawUnexpectedNodesSyntax? = nil, 
      conditions: RawConditionElementListSyntax, 
      _ unexpectedBetweenConditionsAndBody: RawUnexpectedNodesSyntax? = nil, 
      body: RawCodeBlockSyntax, 
      _ unexpectedBetweenBodyAndElseKeyword: RawUnexpectedNodesSyntax? = nil, 
      elseKeyword: RawTokenSyntax?, 
      _ unexpectedBetweenElseKeywordAndElseBody: RawUnexpectedNodesSyntax? = nil, 
      elseBody: ElseBody?, 
      _ unexpectedAfterElseBody: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .ifExpr, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeIfKeyword?.raw
      layout[1] = ifKeyword.raw
      layout[2] = unexpectedBetweenIfKeywordAndConditions?.raw
      layout[3] = conditions.raw
      layout[4] = unexpectedBetweenConditionsAndBody?.raw
      layout[5] = body.raw
      layout[6] = unexpectedBetweenBodyAndElseKeyword?.raw
      layout[7] = elseKeyword?.raw
      layout[8] = unexpectedBetweenElseKeywordAndElseBody?.raw
      layout[9] = elseBody?.raw
      layout[10] = unexpectedAfterElseBody?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeIfKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var ifKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenIfKeywordAndConditions: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var conditions: RawConditionElementListSyntax {
    layoutView.children[3].map(RawConditionElementListSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenConditionsAndBody: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var body: RawCodeBlockSyntax {
    layoutView.children[5].map(RawCodeBlockSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenBodyAndElseKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elseKeyword: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenElseKeywordAndElseBody: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var elseBody: RawSyntax? {
    layoutView.children[9]
  }
  
  public var unexpectedAfterElseBody: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawImplementsAttributeArgumentsSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .implementsAttributeArguments
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
      _ unexpectedBetweenTypeAndComma: RawUnexpectedNodesSyntax? = nil, 
      comma: RawTokenSyntax, 
      _ unexpectedBetweenCommaAndDeclName: RawUnexpectedNodesSyntax? = nil, 
      declName: RawDeclReferenceExprSyntax, 
      _ unexpectedAfterDeclName: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .implementsAttributeArguments, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeType?.raw
      layout[1] = type.raw
      layout[2] = unexpectedBetweenTypeAndComma?.raw
      layout[3] = comma.raw
      layout[4] = unexpectedBetweenCommaAndDeclName?.raw
      layout[5] = declName.raw
      layout[6] = unexpectedAfterDeclName?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenTypeAndComma: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var comma: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenCommaAndDeclName: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var declName: RawDeclReferenceExprSyntax {
    layoutView.children[5].map(RawDeclReferenceExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterDeclName: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawImplicitlyUnwrappedOptionalTypeSyntax: RawTypeSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .implicitlyUnwrappedOptionalType
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
      _ unexpectedBetweenWrappedTypeAndExclamationMark: RawUnexpectedNodesSyntax? = nil, 
      exclamationMark: RawTokenSyntax, 
      _ unexpectedAfterExclamationMark: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .implicitlyUnwrappedOptionalType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeWrappedType?.raw
      layout[1] = wrappedType.raw
      layout[2] = unexpectedBetweenWrappedTypeAndExclamationMark?.raw
      layout[3] = exclamationMark.raw
      layout[4] = unexpectedAfterExclamationMark?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeWrappedType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var wrappedType: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenWrappedTypeAndExclamationMark: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var exclamationMark: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedAfterExclamationMark: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawImportDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .importDecl
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
      _ unexpectedBetweenModifiersAndImportKeyword: RawUnexpectedNodesSyntax? = nil, 
      importKeyword: RawTokenSyntax, 
      _ unexpectedBetweenImportKeywordAndImportKindSpecifier: RawUnexpectedNodesSyntax? = nil, 
      importKindSpecifier: RawTokenSyntax?, 
      _ unexpectedBetweenImportKindSpecifierAndPath: RawUnexpectedNodesSyntax? = nil, 
      path: RawImportPathComponentListSyntax, 
      _ unexpectedAfterPath: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .importDecl, uninitializedCount: 11, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndImportKeyword?.raw
      layout[5] = importKeyword.raw
      layout[6] = unexpectedBetweenImportKeywordAndImportKindSpecifier?.raw
      layout[7] = importKindSpecifier?.raw
      layout[8] = unexpectedBetweenImportKindSpecifierAndPath?.raw
      layout[9] = path.raw
      layout[10] = unexpectedAfterPath?.raw
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
  
  public var unexpectedBetweenModifiersAndImportKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var importKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenImportKeywordAndImportKindSpecifier: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var importKindSpecifier: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenImportKindSpecifierAndPath: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var path: RawImportPathComponentListSyntax {
    layoutView.children[9].map(RawImportPathComponentListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterPath: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawImportPathComponentListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .importPathComponentList
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
  public init(elements: [RawImportPathComponentSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .importPathComponentList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawImportPathComponentSyntax] {
    layoutView.children.map {
      RawImportPathComponentSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawImportPathComponentSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .importPathComponent
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
      _ unexpectedBetweenNameAndTrailingPeriod: RawUnexpectedNodesSyntax? = nil, 
      trailingPeriod: RawTokenSyntax?, 
      _ unexpectedAfterTrailingPeriod: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .importPathComponent, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeName?.raw
      layout[1] = name.raw
      layout[2] = unexpectedBetweenNameAndTrailingPeriod?.raw
      layout[3] = trailingPeriod?.raw
      layout[4] = unexpectedAfterTrailingPeriod?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeName: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var name: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenNameAndTrailingPeriod: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var trailingPeriod: RawTokenSyntax? {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedAfterTrailingPeriod: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawInOutExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .inOutExpr
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
      _ unexpectedBeforeAmpersand: RawUnexpectedNodesSyntax? = nil, 
      ampersand: RawTokenSyntax, 
      _ unexpectedBetweenAmpersandAndExpression: RawUnexpectedNodesSyntax? = nil, 
      expression: RawExprSyntax, 
      _ unexpectedAfterExpression: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .inOutExpr, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAmpersand?.raw
      layout[1] = ampersand.raw
      layout[2] = unexpectedBetweenAmpersandAndExpression?.raw
      layout[3] = expression.raw
      layout[4] = unexpectedAfterExpression?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeAmpersand: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var ampersand: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenAmpersandAndExpression: RawUnexpectedNodesSyntax? {
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
public struct RawInfixOperatorExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .infixOperatorExpr
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
      _ unexpectedBeforeLeftOperand: RawUnexpectedNodesSyntax? = nil, 
      leftOperand: RawExprSyntax, 
      _ unexpectedBetweenLeftOperandAndOperator: RawUnexpectedNodesSyntax? = nil, 
      operator: RawExprSyntax, 
      _ unexpectedBetweenOperatorAndRightOperand: RawUnexpectedNodesSyntax? = nil, 
      rightOperand: RawExprSyntax, 
      _ unexpectedAfterRightOperand: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .infixOperatorExpr, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeLeftOperand?.raw
      layout[1] = leftOperand.raw
      layout[2] = unexpectedBetweenLeftOperandAndOperator?.raw
      layout[3] = `operator`.raw
      layout[4] = unexpectedBetweenOperatorAndRightOperand?.raw
      layout[5] = rightOperand.raw
      layout[6] = unexpectedAfterRightOperand?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeLeftOperand: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var leftOperand: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenLeftOperandAndOperator: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var `operator`: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenOperatorAndRightOperand: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var rightOperand: RawExprSyntax {
    layoutView.children[5].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterRightOperand: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawInheritanceClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .inheritanceClause
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
      _ unexpectedBetweenColonAndInheritedTypes: RawUnexpectedNodesSyntax? = nil, 
      inheritedTypes: RawInheritedTypeListSyntax, 
      _ unexpectedAfterInheritedTypes: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .inheritanceClause, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeColon?.raw
      layout[1] = colon.raw
      layout[2] = unexpectedBetweenColonAndInheritedTypes?.raw
      layout[3] = inheritedTypes.raw
      layout[4] = unexpectedAfterInheritedTypes?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeColon: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var colon: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenColonAndInheritedTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var inheritedTypes: RawInheritedTypeListSyntax {
    layoutView.children[3].map(RawInheritedTypeListSyntax.init(raw:))!
  }
  
  public var unexpectedAfterInheritedTypes: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawInheritedTypeListSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .inheritedTypeList
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
  public init(elements: [RawInheritedTypeSyntax], arena: __shared SyntaxArena) {
    let raw = RawSyntax.makeLayout(
      kind: .inheritedTypeList, uninitializedCount: elements.count, arena: arena) { layout in
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
  public var elements: [RawInheritedTypeSyntax] {
    layoutView.children.map {
      RawInheritedTypeSyntax(raw: $0!)
    }
  }
}

@_spi(RawSyntax)
@frozen
public struct RawInheritedTypeSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .inheritedType
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
      _ unexpectedBetweenTypeAndTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      trailingComma: RawTokenSyntax?, 
      _ unexpectedAfterTrailingComma: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .inheritedType, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeType?.raw
      layout[1] = type.raw
      layout[2] = unexpectedBetweenTypeAndTrailingComma?.raw
      layout[3] = trailingComma?.raw
      layout[4] = unexpectedAfterTrailingComma?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeType: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[1].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenTypeAndTrailingComma: RawUnexpectedNodesSyntax? {
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
public struct RawInitializerClauseSyntax: RawSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .initializerClause
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
      _ unexpectedBetweenEqualAndValue: RawUnexpectedNodesSyntax? = nil, 
      value: RawExprSyntax, 
      _ unexpectedAfterValue: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .initializerClause, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeEqual?.raw
      layout[1] = equal.raw
      layout[2] = unexpectedBetweenEqualAndValue?.raw
      layout[3] = value.raw
      layout[4] = unexpectedAfterValue?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeEqual: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var equal: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenEqualAndValue: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var value: RawExprSyntax {
    layoutView.children[3].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedAfterValue: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawInitializerDeclSyntax: RawDeclSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .initializerDecl
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
      _ unexpectedBetweenModifiersAndInitKeyword: RawUnexpectedNodesSyntax? = nil, 
      initKeyword: RawTokenSyntax, 
      _ unexpectedBetweenInitKeywordAndOptionalMark: RawUnexpectedNodesSyntax? = nil, 
      optionalMark: RawTokenSyntax?, 
      _ unexpectedBetweenOptionalMarkAndGenericParameterClause: RawUnexpectedNodesSyntax? = nil, 
      genericParameterClause: RawGenericParameterClauseSyntax?, 
      _ unexpectedBetweenGenericParameterClauseAndSignature: RawUnexpectedNodesSyntax? = nil, 
      signature: RawFunctionSignatureSyntax, 
      _ unexpectedBetweenSignatureAndGenericWhereClause: RawUnexpectedNodesSyntax? = nil, 
      genericWhereClause: RawGenericWhereClauseSyntax?, 
      _ unexpectedBetweenGenericWhereClauseAndBody: RawUnexpectedNodesSyntax? = nil, 
      body: RawCodeBlockSyntax?, 
      _ unexpectedAfterBody: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .initializerDecl, uninitializedCount: 17, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeAttributes?.raw
      layout[1] = attributes.raw
      layout[2] = unexpectedBetweenAttributesAndModifiers?.raw
      layout[3] = modifiers.raw
      layout[4] = unexpectedBetweenModifiersAndInitKeyword?.raw
      layout[5] = initKeyword.raw
      layout[6] = unexpectedBetweenInitKeywordAndOptionalMark?.raw
      layout[7] = optionalMark?.raw
      layout[8] = unexpectedBetweenOptionalMarkAndGenericParameterClause?.raw
      layout[9] = genericParameterClause?.raw
      layout[10] = unexpectedBetweenGenericParameterClauseAndSignature?.raw
      layout[11] = signature.raw
      layout[12] = unexpectedBetweenSignatureAndGenericWhereClause?.raw
      layout[13] = genericWhereClause?.raw
      layout[14] = unexpectedBetweenGenericWhereClauseAndBody?.raw
      layout[15] = body?.raw
      layout[16] = unexpectedAfterBody?.raw
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
  
  public var unexpectedBetweenModifiersAndInitKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var initKeyword: RawTokenSyntax {
    layoutView.children[5].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenInitKeywordAndOptionalMark: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var optionalMark: RawTokenSyntax? {
    layoutView.children[7].map(RawTokenSyntax.init(raw:))
  }
  
  public var unexpectedBetweenOptionalMarkAndGenericParameterClause: RawUnexpectedNodesSyntax? {
    layoutView.children[8].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericParameterClause: RawGenericParameterClauseSyntax? {
    layoutView.children[9].map(RawGenericParameterClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenGenericParameterClauseAndSignature: RawUnexpectedNodesSyntax? {
    layoutView.children[10].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var signature: RawFunctionSignatureSyntax {
    layoutView.children[11].map(RawFunctionSignatureSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenSignatureAndGenericWhereClause: RawUnexpectedNodesSyntax? {
    layoutView.children[12].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var genericWhereClause: RawGenericWhereClauseSyntax? {
    layoutView.children[13].map(RawGenericWhereClauseSyntax.init(raw:))
  }
  
  public var unexpectedBetweenGenericWhereClauseAndBody: RawUnexpectedNodesSyntax? {
    layoutView.children[14].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var body: RawCodeBlockSyntax? {
    layoutView.children[15].map(RawCodeBlockSyntax.init(raw:))
  }
  
  public var unexpectedAfterBody: RawUnexpectedNodesSyntax? {
    layoutView.children[16].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIntegerLiteralExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .integerLiteralExpr
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
      kind: .integerLiteralExpr, uninitializedCount: 3, arena: arena) { layout in
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
public struct RawIsExprSyntax: RawExprSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .isExpr
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
      _ unexpectedBetweenExpressionAndIsKeyword: RawUnexpectedNodesSyntax? = nil, 
      isKeyword: RawTokenSyntax, 
      _ unexpectedBetweenIsKeywordAndType: RawUnexpectedNodesSyntax? = nil, 
      type: RawTypeSyntax, 
      _ unexpectedAfterType: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .isExpr, uninitializedCount: 7, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeExpression?.raw
      layout[1] = expression.raw
      layout[2] = unexpectedBetweenExpressionAndIsKeyword?.raw
      layout[3] = isKeyword.raw
      layout[4] = unexpectedBetweenIsKeywordAndType?.raw
      layout[5] = type.raw
      layout[6] = unexpectedAfterType?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeExpression: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var expression: RawExprSyntax {
    layoutView.children[1].map(RawExprSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenExpressionAndIsKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var isKeyword: RawTokenSyntax {
    layoutView.children[3].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenIsKeywordAndType: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[5].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterType: RawUnexpectedNodesSyntax? {
    layoutView.children[6].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}

@_spi(RawSyntax)
@frozen
public struct RawIsTypePatternSyntax: RawPatternSyntaxNodeProtocol {
  @inlinable
  public var layoutView: RawSyntaxLayoutView {
    return raw.layoutView!
  }
  
  @inlinable public static func isKindOf(_ raw: RawSyntax) -> Bool {
    return raw.kind == .isTypePattern
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
      _ unexpectedBeforeIsKeyword: RawUnexpectedNodesSyntax? = nil, 
      isKeyword: RawTokenSyntax, 
      _ unexpectedBetweenIsKeywordAndType: RawUnexpectedNodesSyntax? = nil, 
      type: RawTypeSyntax, 
      _ unexpectedAfterType: RawUnexpectedNodesSyntax? = nil, 
      arena: __shared SyntaxArena
    ) {
    let raw = RawSyntax.makeLayout(
      kind: .isTypePattern, uninitializedCount: 5, arena: arena) { layout in
      layout.initialize(repeating: nil)
      layout[0] = unexpectedBeforeIsKeyword?.raw
      layout[1] = isKeyword.raw
      layout[2] = unexpectedBetweenIsKeywordAndType?.raw
      layout[3] = type.raw
      layout[4] = unexpectedAfterType?.raw
    }
    self.init(unchecked: raw)
  }
  
  public var unexpectedBeforeIsKeyword: RawUnexpectedNodesSyntax? {
    layoutView.children[0].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var isKeyword: RawTokenSyntax {
    layoutView.children[1].map(RawTokenSyntax.init(raw:))!
  }
  
  public var unexpectedBetweenIsKeywordAndType: RawUnexpectedNodesSyntax? {
    layoutView.children[2].map(RawUnexpectedNodesSyntax.init(raw:))
  }
  
  public var type: RawTypeSyntax {
    layoutView.children[3].map(RawTypeSyntax.init(raw:))!
  }
  
  public var unexpectedAfterType: RawUnexpectedNodesSyntax? {
    layoutView.children[4].map(RawUnexpectedNodesSyntax.init(raw:))
  }
}
