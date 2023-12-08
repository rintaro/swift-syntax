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

@_spi(RawSyntax) @_spi(ExperimentalLanguageFeatures) import SwiftSyntax

/// A set of `TokenSpecs`. We expect to consume one of the sets specs in the
/// parser.
protocol TokenSpecSet: CaseIterable {
  var spec: TokenSpec { get }

  /// Creates an instance if `lexeme` satisfies the condition of this subset,
  /// taking into account any `experimentalFeatures` active.
  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures)
}

/// A way to combine two token spec sets into an aggregate token spec set.
enum EitherTokenSpecSet<LHS: TokenSpecSet, RHS: TokenSpecSet>: TokenSpecSet {
  case lhs(LHS)
  case rhs(RHS)

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    if let x = LHS(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .lhs(x)
      return
    }
    if let y = RHS(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .rhs(y)
      return
    }

    return nil
  }

  var spec: TokenSpec {
    switch self {
    case .lhs(let x):
      return x.spec
    case .rhs(let y):
      return y.spec
    }
  }

  static var allCases: [EitherTokenSpecSet] {
    return LHS.allCases.map(Self.lhs) + RHS.allCases.map(Self.rhs)
  }
}

// MARK: - Subsets

enum AccessorModifier: TokenSpecSet {
  case __consuming
  case consuming
  case borrowing
  case mutating
  case nonmutating

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.__consumingKeyword): self = .__consuming
    case TokenSpec(.consumingKeyword): self = .consuming
    case TokenSpec(.borrowingKeyword): self = .borrowing
    case TokenSpec(.mutatingKeyword): self = .mutating
    case TokenSpec(.nonmutatingKeyword): self = .nonmutating
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .__consuming: return .__consumingKeyword
    case .consuming: return .consumingKeyword
    case .borrowing: return .borrowingKeyword
    case .mutating: return .mutatingKeyword
    case .nonmutating: return .nonmutatingKeyword
    }
  }
}

enum CanBeStatementStart: TokenSpecSet {
  case `break`
  case `continue`
  case `defer`
  case `do`
  case `fallthrough`
  case `for`
  case discard
  case `guard`
  case `if`
  case `repeat`
  case `return`
  case `switch`
  case then
  case `throw`
  case `while`
  case yield

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.breakKeyword): self = .break
    case TokenSpec(.continueKeyword): self = .continue
    case TokenSpec(.deferKeyword): self = .defer
    case TokenSpec(.doKeyword): self = .do
    case TokenSpec(.fallthroughKeyword): self = .fallthrough
    case TokenSpec(.forKeyword): self = .for
    case TokenSpec(.discardKeyword): self = .discard
    case TokenSpec(.guardKeyword): self = .guard
    case TokenSpec(.ifKeyword): self = .if
    case TokenSpec(.repeatKeyword): self = .repeat
    case TokenSpec(.returnKeyword): self = .return
    case TokenSpec(.switchKeyword): self = .switch
    case TokenSpec(.thenKeyword): self = .then
    case TokenSpec(.throwKeyword): self = .throw
    case TokenSpec(.whileKeyword): self = .while
    case TokenSpec(.yieldKeyword): self = .yield
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .break: return .breakKeyword
    case .continue: return .continueKeyword
    case .defer: return .deferKeyword
    case .do: return .doKeyword
    case .fallthrough: return .fallthroughKeyword
    case .for: return .forKeyword
    case .discard: return TokenSpec(.discardKeyword, recoveryPrecedence: .stmtKeyword)
    case .guard: return .guardKeyword
    case .if: return .ifKeyword
    case .repeat: return .repeatKeyword
    case .return: return .returnKeyword
    case .switch: return .switchKeyword
    case .then: return .thenKeyword
    case .throw: return .throwKeyword
    case .while: return .whileKeyword
    case .yield: return .yieldKeyword
    }
  }
}

enum CompilationCondition: TokenSpecSet {
  case swift
  case compiler
  case canImport

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.swiftKeyword): self = .swift
    case TokenSpec(.compilerKeyword): self = .compiler
    case TokenSpec(.canImportKeyword): self = .canImport
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .swift: return .swiftKeyword
    case .compiler: return .compilerKeyword
    case .canImport: return .canImportKeyword
    }
  }

}

enum ContextualDeclKeyword: TokenSpecSet {
  case __consuming
  case _compilerInitialized
  case _const
  case _local
  case actor
  case async
  case convenience
  case distributed
  case dynamic
  case final
  case indirect
  case infix
  case isolated
  case lazy
  case mutating
  case nonisolated
  case nonmutating
  case package
  case open
  case optional
  case override
  case postfix
  case prefix
  case required
  case unowned
  case weak

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.__consumingKeyword): self = .__consuming
    case TokenSpec(._compilerInitializedKeyword): self = ._compilerInitialized
    case TokenSpec(._constKeyword): self = ._const
    case TokenSpec(._localKeyword): self = ._local
    case TokenSpec(.actorKeyword): self = .actor
    case TokenSpec(.asyncKeyword): self = .async
    case TokenSpec(.convenienceKeyword): self = .convenience
    case TokenSpec(.distributedKeyword): self = .distributed
    case TokenSpec(.dynamicKeyword): self = .dynamic
    case TokenSpec(.finalKeyword): self = .final
    case TokenSpec(.indirectKeyword): self = .indirect
    case TokenSpec(.infixKeyword): self = .infix
    case TokenSpec(.isolatedKeyword): self = .isolated
    case TokenSpec(.lazyKeyword): self = .lazy
    case TokenSpec(.mutatingKeyword): self = .mutating
    case TokenSpec(.nonisolatedKeyword): self = .nonisolated
    case TokenSpec(.nonmutatingKeyword): self = .nonmutating
    case TokenSpec(.packageKeyword): self = .package
    case TokenSpec(.openKeyword): self = .open
    case TokenSpec(.optionalKeyword): self = .optional
    case TokenSpec(.overrideKeyword): self = .override
    case TokenSpec(.postfixKeyword): self = .postfix
    case TokenSpec(.prefixKeyword): self = .prefix
    case TokenSpec(.requiredKeyword): self = .required
    case TokenSpec(.unownedKeyword): self = .unowned
    case TokenSpec(.weakKeyword): self = .weak
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .__consuming: return .__consumingKeyword
    case ._compilerInitialized: return ._compilerInitializedKeyword
    case ._const: return ._constKeyword
    case ._local: return ._localKeyword
    case .actor: return .actorKeyword
    case .async: return .asyncKeyword
    case .convenience: return .convenienceKeyword
    case .distributed: return .distributedKeyword
    case .dynamic: return .dynamicKeyword
    case .final: return .finalKeyword
    case .indirect: return .indirectKeyword
    case .infix: return .infixKeyword
    case .isolated: return .isolatedKeyword
    case .lazy: return .lazyKeyword
    case .mutating: return .mutatingKeyword
    case .nonisolated: return .nonisolatedKeyword
    case .nonmutating: return .nonmutatingKeyword
    case .package: return .packageKeyword
    case .open: return .openKeyword
    case .optional: return .optionalKeyword
    case .override: return .overrideKeyword
    case .postfix: return .postfixKeyword
    case .prefix: return .prefixKeyword
    case .required: return .requiredKeyword
    case .unowned: return .unownedKeyword
    case .weak: return .weakKeyword
    }
  }
}

/// A `DeclarationKeyword` that is not a `ValueBindingPatternSyntax.BindingSpecifierOptions`.
///
/// `ValueBindingPatternSyntax.BindingSpecifierOptions` are injected into
/// `DeclarationKeyword` via an `EitherTokenSpecSet`.
enum PureDeclarationKeyword: TokenSpecSet {
  case actor
  case `associatedtype`
  case `case`
  case `class`
  case `deinit`
  case `enum`
  case `extension`
  case `func`
  case `import`
  case `init`
  case macro
  case `operator`
  case `precedencegroup`
  case `protocol`
  case `struct`
  case `subscript`
  case `typealias`
  case pound

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.actorKeyword): self = .actor
    case TokenSpec(.macroKeyword): self = .macro
    case TokenSpec(.associatedtypeKeyword): self = .associatedtype
    case TokenSpec(.caseKeyword): self = .case
    case TokenSpec(.classKeyword): self = .class
    case TokenSpec(.deinitKeyword): self = .deinit
    case TokenSpec(.enumKeyword): self = .enum
    case TokenSpec(.extensionKeyword): self = .extension
    case TokenSpec(.funcKeyword): self = .func
    case TokenSpec(.importKeyword): self = .import
    case TokenSpec(.initKeyword): self = .`init`
    case TokenSpec(.operatorKeyword): self = .operator
    case TokenSpec(.precedencegroupKeyword): self = .precedencegroup
    case TokenSpec(.protocolKeyword): self = .protocol
    case TokenSpec(.structKeyword): self = .struct
    case TokenSpec(.subscriptKeyword): self = .subscript
    case TokenSpec(.typealiasKeyword): self = .typealias
    case TokenSpec(.pound): self = .pound
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .actor: return TokenSpec(.actorKeyword, recoveryPrecedence: .declKeyword)
    case .associatedtype: return .associatedtypeKeyword
    case .case: return TokenSpec(.caseKeyword, recoveryPrecedence: .declKeyword)
    case .class: return .classKeyword
    case .deinit: return .deinitKeyword
    case .enum: return .enumKeyword
    case .extension: return .extensionKeyword
    case .func: return .funcKeyword
    case .import: return .importKeyword
    case .`init`: return .initKeyword
    case .macro: return TokenSpec(.macroKeyword, recoveryPrecedence: .declKeyword)
    case .operator: return .operatorKeyword
    case .precedencegroup: return .precedencegroupKeyword
    case .protocol: return .protocolKeyword
    case .struct: return .structKeyword
    case .subscript: return .subscriptKeyword
    case .typealias: return .typealiasKeyword
    case .pound: return TokenSpec(.pound, recoveryPrecedence: .openingPoundIf)
    }
  }
}

typealias DeclarationKeyword = EitherTokenSpecSet<
  PureDeclarationKeyword,
  ValueBindingPatternSyntax.BindingSpecifierOptions
>

enum DeclarationModifier: TokenSpecSet {
  case __consuming
  case __setter_access
  case _const
  case _local
  case async
  case borrowing
  case `class`
  case consuming
  case convenience
  case distributed
  case dynamic
  case `fileprivate`
  case final
  case indirect
  case infix
  case `internal`
  case isolated
  case lazy
  case mutating
  case nonisolated
  case nonmutating
  case open
  case optional
  case override
  case package
  case postfix
  case prefix
  case `private`
  case `public`
  case reasync
  case required
  case `rethrows`
  case `static`
  case unowned
  case weak
  case _resultDependsOn
  case _resultDependsOnSelf

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.__consumingKeyword): self = .__consuming
    case TokenSpec(.__setter_accessKeyword): self = .__setter_access
    case TokenSpec(._constKeyword): self = ._const
    case TokenSpec(._localKeyword): self = ._local
    case TokenSpec(.asyncKeyword): self = .async
    case TokenSpec(.borrowingKeyword): self = .borrowing
    case TokenSpec(.classKeyword): self = .class
    case TokenSpec(.consumingKeyword): self = .consuming
    case TokenSpec(.convenienceKeyword): self = .convenience
    case TokenSpec(.distributedKeyword): self = .distributed
    case TokenSpec(.dynamicKeyword): self = .dynamic
    case TokenSpec(.fileprivateKeyword): self = .fileprivate
    case TokenSpec(.finalKeyword): self = .final
    case TokenSpec(.indirectKeyword): self = .indirect
    case TokenSpec(.infixKeyword): self = .infix
    case TokenSpec(.internalKeyword): self = .internal
    case TokenSpec(.isolatedKeyword): self = .isolated
    case TokenSpec(.lazyKeyword): self = .lazy
    case TokenSpec(.mutatingKeyword): self = .mutating
    case TokenSpec(.nonisolatedKeyword): self = .nonisolated
    case TokenSpec(.nonmutatingKeyword): self = .nonmutating
    case TokenSpec(.openKeyword): self = .open
    case TokenSpec(.optionalKeyword): self = .optional
    case TokenSpec(.overrideKeyword): self = .override
    case TokenSpec(.packageKeyword): self = .package
    case TokenSpec(.postfixKeyword): self = .postfix
    case TokenSpec(.prefixKeyword): self = .prefix
    case TokenSpec(.privateKeyword): self = .private
    case TokenSpec(.publicKeyword): self = .public
    case TokenSpec(.reasyncKeyword): self = .reasync
    case TokenSpec(.requiredKeyword): self = .required
    case TokenSpec(.rethrowsKeyword): self = .rethrows
    case TokenSpec(.staticKeyword): self = .static
    case TokenSpec(.unownedKeyword): self = .unowned
    case TokenSpec(.weakKeyword): self = .weak
    case TokenSpec(._resultDependsOnKeyword) where experimentalFeatures.contains(.nonEscapableTypes): self = ._resultDependsOn
    case TokenSpec(._resultDependsOnSelfKeyword) where experimentalFeatures.contains(.nonEscapableTypes): self = ._resultDependsOnSelf
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .__consuming: return .__consumingKeyword
    case .__setter_access: return .__setter_accessKeyword
    case ._const: return TokenSpec(._constKeyword, recoveryPrecedence: .declKeyword)
    case ._local: return ._localKeyword
    case .async: return TokenSpec(.asyncKeyword, recoveryPrecedence: .declKeyword)
    case .borrowing: return TokenSpec(.borrowingKeyword, recoveryPrecedence: .declKeyword)
    case .class: return .classKeyword
    case .consuming: return TokenSpec(.consumingKeyword, recoveryPrecedence: .declKeyword)
    case .convenience: return .convenienceKeyword
    case .distributed: return .distributedKeyword
    case .dynamic: return .dynamicKeyword
    case .fileprivate: return .fileprivateKeyword
    case .final: return .finalKeyword
    case .indirect: return .indirectKeyword
    case .infix: return .infixKeyword
    case .internal: return .internalKeyword
    case .isolated: return TokenSpec(.isolatedKeyword, recoveryPrecedence: .declKeyword)
    case .lazy: return .lazyKeyword
    case .mutating: return .mutatingKeyword
    case .nonisolated: return .nonisolatedKeyword
    case .nonmutating: return .nonmutatingKeyword
    case .open: return .openKeyword
    case .optional: return .optionalKeyword
    case .override: return .overrideKeyword
    case .package: return .packageKeyword
    case .postfix: return .postfixKeyword
    case .prefix: return .prefixKeyword
    case .private: return .privateKeyword
    case .public: return .publicKeyword
    case .reasync: return TokenSpec(.reasyncKeyword, recoveryPrecedence: .declKeyword)
    case .required: return .requiredKeyword
    case .rethrows: return TokenSpec(.rethrowsKeyword, recoveryPrecedence: .declKeyword)
    case .static: return .staticKeyword
    case .unowned: return TokenSpec(.unownedKeyword, recoveryPrecedence: .declKeyword)
    case .weak: return TokenSpec(.weakKeyword, recoveryPrecedence: .declKeyword)
    case ._resultDependsOn: return TokenSpec(._resultDependsOnKeyword, recoveryPrecedence: .declKeyword)
    case ._resultDependsOnSelf: return TokenSpec(._resultDependsOnSelfKeyword, recoveryPrecedence: .declKeyword)
    }
  }
}

/// Union of the following token kind subsets:
///  - `DeclarationModifier`
///  - `DeclarationKeyword`
enum DeclarationStart: TokenSpecSet {
  case declarationModifier(DeclarationModifier)
  case declarationKeyword(DeclarationKeyword)

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    if let subset = DeclarationModifier(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .declarationModifier(subset)
    } else if let subset = DeclarationKeyword(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .declarationKeyword(subset)
    } else {
      return nil
    }
  }

  static var allCases: [DeclarationStart] {
    return DeclarationModifier.allCases.map(Self.declarationModifier) + DeclarationKeyword.allCases.map(Self.declarationKeyword)
  }

  var spec: TokenSpec {
    switch self {
    case .declarationModifier(let underlyingKind): return underlyingKind.spec
    case .declarationKeyword(let underlyingKind): return underlyingKind.spec
    }
  }
}

enum Operator: TokenSpecSet {
  case binaryOperator
  case postfixOperator
  case prefixOperator

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    // NOTE: If you ever add any experimental features here,
    // `isContextualPunctuator` will need updating to handle that.
    switch lexeme.rawTokenKind {
    case .binaryOperator: self = .binaryOperator
    case .postfixOperator: self = .postfixOperator
    case .prefixOperator: self = .prefixOperator
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .binaryOperator: return .binaryOperator
    case .postfixOperator: return .postfixOperator
    case .prefixOperator: return .prefixOperator
    }
  }
}

/// Tokens that are either binary operators, or can act like binary operators.
enum BinaryOperatorLike: TokenSpecSet {
  case binaryOperator
  case infixQuestionMark
  case equal
  case arrow

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme.rawTokenKind {
    case .binaryOperator: self = .binaryOperator
    case .infixQuestionMark: self = .infixQuestionMark
    case .equal: self = .equal
    case .arrow: self = .arrow
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .binaryOperator: return .binaryOperator
    case .infixQuestionMark: return TokenSpec(.infixQuestionMark, remapping: .binaryOperator)
    case .equal: return TokenSpec(.equal, remapping: .binaryOperator)
    case .arrow: return TokenSpec(.arrow, remapping: .binaryOperator)
    }
  }
}

/// Tokens that are either postfix operators, or can act like postfix operators.
enum PostfixOperatorLike: TokenSpecSet {
  case postfixOperator
  case exclamationMark
  case postfixQuestionMark

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme.rawTokenKind {
    case .postfixOperator: self = .postfixOperator
    case .exclamationMark: self = .exclamationMark
    case .postfixQuestionMark: self = .postfixQuestionMark
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .postfixOperator: return .postfixOperator
    case .exclamationMark: return TokenSpec(.exclamationMark, remapping: .postfixOperator)
    case .postfixQuestionMark: return TokenSpec(.postfixQuestionMark, remapping: .postfixOperator)
    }
  }
}

/// Tokens that can be used in operator declarations.
enum OperatorLike: TokenSpecSet {
  case prefixOperator
  case binaryOperatorLike(BinaryOperatorLike)
  case postfixOperatorLike(PostfixOperatorLike)

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    if case .prefixOperator = lexeme.rawTokenKind {
      self = .prefixOperator
      return
    }
    if let binOp = BinaryOperatorLike(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .binaryOperatorLike(binOp)
      return
    }
    if let postfixOp = PostfixOperatorLike(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .postfixOperatorLike(postfixOp)
      return
    }
    return nil
  }

  static var allCases: [OperatorLike] {
    [.prefixOperator] + BinaryOperatorLike.allCases.map(Self.binaryOperatorLike) + PostfixOperatorLike.allCases.map(Self.postfixOperatorLike)
  }

  var spec: TokenSpec {
    switch self {
    case .prefixOperator: return .prefixOperator
    case .binaryOperatorLike(let op): return op.spec
    case .postfixOperatorLike(let op): return op.spec
    }
  }
}

enum SwitchCaseStart: TokenSpecSet {
  case `case`
  case `default`

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.caseKeyword): self = .case
    case TokenSpec(.defaultKeyword): self = .default
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .case: return .caseKeyword
    case .default: return .defaultKeyword
    }
  }
}

enum TypeAttribute: TokenSpecSet {
  case _local
  case _noMetadata
  case _opaqueReturnTypeOf
  case async
  case autoclosure
  case convention
  case differentiable
  case escaping
  case noDerivative
  case noescape
  case retroactive
  case Sendable
  case unchecked

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(._localKeyword): self = ._local
    case TokenSpec(._noMetadataKeyword): self = ._noMetadata
    case TokenSpec(._opaqueReturnTypeOfKeyword): self = ._opaqueReturnTypeOf
    case TokenSpec(.asyncKeyword): self = .async
    case TokenSpec(.autoclosureKeyword): self = .autoclosure
    case TokenSpec(.conventionKeyword): self = .convention
    case TokenSpec(.differentiableKeyword): self = .differentiable
    case TokenSpec(.escapingKeyword): self = .escaping
    case TokenSpec(.noDerivativeKeyword): self = .noDerivative
    case TokenSpec(.noescapeKeyword): self = .noescape
    case TokenSpec(.SendableKeyword): self = .Sendable
    case TokenSpec(.retroactiveKeyword): self = .retroactive
    case TokenSpec(.uncheckedKeyword): self = .unchecked
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case ._local: return ._localKeyword
    case ._noMetadata: return ._noMetadataKeyword
    case ._opaqueReturnTypeOf: return ._opaqueReturnTypeOfKeyword
    case .async: return .asyncKeyword
    case .autoclosure: return .autoclosureKeyword
    case .convention: return .conventionKeyword
    case .differentiable: return .differentiableKeyword
    case .escaping: return .escapingKeyword
    case .noDerivative: return .noDerivativeKeyword
    case .noescape: return .noescapeKeyword
    case .retroactive: return .retroactiveKeyword
    case .Sendable: return .SendableKeyword
    case .unchecked: return .uncheckedKeyword
    }
  }
}

@_spi(Diagnostics)
public enum TypeSpecifier: TokenSpecSet {
  case `inout`
  case owned
  case shared
  case borrowing
  case consuming

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.inoutKeyword): self = .inout
    case TokenSpec(.__ownedKeyword): self = .owned
    case TokenSpec(.__sharedKeyword): self = .shared
    case TokenSpec(.consumingKeyword): self = .consuming
    case TokenSpec(.borrowingKeyword): self = .borrowing
    default: return nil
    }
  }

  @_spi(Diagnostics)
  public init?(token: TokenSyntax) {
    switch token {
    case TokenSpec(.inoutKeyword): self = .inout
    case TokenSpec(.__ownedKeyword): self = .owned
    case TokenSpec(.__sharedKeyword): self = .shared
    case TokenSpec(.consumingKeyword): self = .shared
    case TokenSpec(.borrowingKeyword): self = .shared
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .inout: return .inoutKeyword
    case .owned: return .__ownedKeyword
    case .shared: return .__sharedKeyword
    case .borrowing: return .borrowingKeyword
    case .consuming: return .consumingKeyword
    }
  }
}

// MARK: Expression start

enum ExpressionModifierKeyword: TokenSpecSet {
  case await
  case _move
  case _borrow
  case `try`
  case consume
  case copy
  case `repeat`
  case each
  case any

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.awaitKeyword): self = .await
    case TokenSpec(._moveKeyword): self = ._move
    case TokenSpec(._borrowKeyword): self = ._borrow
    case TokenSpec(.tryKeyword): self = .try
    case TokenSpec(.consumeKeyword): self = .consume
    case TokenSpec(.copyKeyword): self = .copy
    case TokenSpec(.repeatKeyword): self = .repeat
    case TokenSpec(.eachKeyword): self = .each
    case TokenSpec(.anyKeyword): self = .any
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .await: return .awaitKeyword
    case ._move: return ._moveKeyword
    case ._borrow: return ._borrowKeyword
    case .consume: return .consumeKeyword
    case .copy: return .copyKeyword
    case .try: return .tryKeyword
    case .repeat: return .repeatKeyword
    case .each: return .eachKeyword
    case .any: return .anyKeyword
    }
  }
}

enum SingleValueStatementExpression: TokenSpecSet {
  case `do`
  case `if`
  case `switch`

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.doKeyword) where experimentalFeatures.contains(.doExpressions): self = .do
    case TokenSpec(.ifKeyword): self = .if
    case TokenSpec(.switchKeyword): self = .switch
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .do: return .doKeyword
    case .if: return .ifKeyword
    case .switch: return .switchKeyword
    }
  }
}

enum ExpressionPrefixOperator: TokenSpecSet {
  case backslash
  case prefixAmpersand
  case prefixOperator

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme.rawTokenKind {
    case .backslash: self = .backslash
    case .prefixAmpersand: self = .prefixAmpersand
    case .prefixOperator: self = .prefixOperator
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .backslash: return .backslash
    case .prefixAmpersand: return .prefixAmpersand
    case .prefixOperator: return .prefixOperator
    }
  }
}

/// A `MatchingPatternStart` that is not a `ValueBindingPatternSyntax.BindingSpecifierOptions`.
///
/// We use an `EitherTokenSpecSet` to inject `ValueBindingPatternSyntax.BindingSpecifierOptions` into
/// `MatchingPatternStart`.
enum PureMatchingPatternStart: TokenSpecSet {
  case `is`

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.isKeyword): self = .is
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .is: return .isKeyword
    }
  }
}

typealias MatchingPatternStart = EitherTokenSpecSet<
  PureMatchingPatternStart,
  ValueBindingPatternSyntax.BindingSpecifierOptions
>

enum ParameterModifier: TokenSpecSet {
  case _const
  case isolated

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(._constKeyword): self = ._const
    case TokenSpec(.isolatedKeyword): self = .isolated
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case ._const: return ._constKeyword
    case .isolated: return .isolatedKeyword
    }
  }
}

enum PrimaryExpressionStart: TokenSpecSet {
  case `Any`
  case atSign  // For recovery
  case `Self`
  case dollarIdentifier
  case `false`
  case floatLiteral
  case identifier
  case `init`
  case integerLiteral
  case leftBrace
  case leftParen
  case leftSquare
  case `nil`
  case period
  case pound
  case poundAvailable  // For recovery
  case poundUnavailable  // For recovery
  case regexSlash
  case extendedRegexDelimiter
  case `self`
  case `super`
  case `true`
  case wildcard
  case rawStringDelimiter
  case stringQuote
  case multilineStringQuote
  case singleQuote

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.AnyKeyword): self = .Any
    case TokenSpec(.atSign): self = .atSign
    case TokenSpec(.SelfKeyword): self = .Self
    case TokenSpec(.dollarIdentifier): self = .dollarIdentifier
    case TokenSpec(.falseKeyword): self = .false
    case TokenSpec(.floatLiteral): self = .floatLiteral
    case TokenSpec(.identifier): self = .identifier
    case TokenSpec(.initKeyword): self = .`init`
    case TokenSpec(.integerLiteral): self = .integerLiteral
    case TokenSpec(.leftBrace): self = .leftBrace
    case TokenSpec(.leftParen): self = .leftParen
    case TokenSpec(.leftSquare): self = .leftSquare
    case TokenSpec(.nilKeyword): self = .nil
    case TokenSpec(.period): self = .period
    case TokenSpec(.pound): self = .pound
    case TokenSpec(.poundAvailable): self = .poundAvailable
    case TokenSpec(.poundUnavailable): self = .poundUnavailable
    case TokenSpec(.regexSlash): self = .regexSlash
    case TokenSpec(.regexPoundDelimiter): self = .extendedRegexDelimiter
    case TokenSpec(.selfKeyword): self = .self
    case TokenSpec(.superKeyword): self = .super
    case TokenSpec(.trueKeyword): self = .true
    case TokenSpec(.wildcard): self = .wildcard
    case TokenSpec(.rawStringPoundDelimiter): self = .rawStringDelimiter
    case TokenSpec(.stringQuote): self = .stringQuote
    case TokenSpec(.multilineStringQuote): self = .multilineStringQuote
    case TokenSpec(.singleQuote): self = .singleQuote
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .Any: return .AnyKeyword
    case .atSign: return .atSign
    case .Self: return .SelfKeyword
    case .dollarIdentifier: return .dollarIdentifier
    case .false: return .falseKeyword
    case .floatLiteral: return .floatLiteral
    case .identifier: return .identifier
    case .`init`: return .initKeyword
    case .integerLiteral: return .integerLiteral
    case .leftBrace: return .leftBrace
    case .leftParen: return .leftParen
    case .leftSquare: return .leftSquare
    case .nil: return .nilKeyword
    case .period: return .period
    case .pound: return .pound
    case .poundAvailable: return .poundAvailable
    case .poundUnavailable: return .poundUnavailable
    case .regexSlash: return .regexSlash
    case .extendedRegexDelimiter: return .regexPoundDelimiter
    case .self: return .selfKeyword
    case .super: return .superKeyword
    case .true: return .trueKeyword
    case .wildcard: return .wildcard
    case .rawStringDelimiter: return .rawStringPoundDelimiter
    case .stringQuote: return .stringQuote
    case .multilineStringQuote: return .multilineStringQuote
    case .singleQuote: return .singleQuote
    }
  }
}

/// Union of the following token kind subsets:
///  - `AwaitTry`
///  - `ExpressionPrefixOperator`
///  - `MatchingPatternStart`
///  - `PrimaryExpressionStart`
enum ExpressionStart: TokenSpecSet {
  case awaitTryMove(ExpressionModifierKeyword)
  case expressionPrefixOperator(ExpressionPrefixOperator)
  case primaryExpressionStart(PrimaryExpressionStart)
  case singleValueStatement(SingleValueStatementExpression)

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    if let subset = ExpressionModifierKeyword(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .awaitTryMove(subset)
    } else if let subset = ExpressionPrefixOperator(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .expressionPrefixOperator(subset)
    } else if let subset = PrimaryExpressionStart(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .primaryExpressionStart(subset)
    } else if let subset = SingleValueStatementExpression(lexeme: lexeme, experimentalFeatures: experimentalFeatures) {
      self = .singleValueStatement(subset)
    } else {
      return nil
    }
  }

  static var allCases: [ExpressionStart] {
    return ExpressionModifierKeyword.allCases.map(Self.awaitTryMove)
      + ExpressionPrefixOperator.allCases.map(Self.expressionPrefixOperator)
      + PrimaryExpressionStart.allCases.map(Self.primaryExpressionStart)
      + SingleValueStatementExpression.allCases.map(Self.singleValueStatement)
  }

  var spec: TokenSpec {
    switch self {
    case .awaitTryMove(let underlyingKind): return underlyingKind.spec
    case .expressionPrefixOperator(let underlyingKind): return underlyingKind.spec
    case .primaryExpressionStart(let underlyingKind): return underlyingKind.spec
    case .singleValueStatement(let underlyingKind): return underlyingKind.spec
    }
  }
}

enum EffectSpecifiers: TokenSpecSet {
  case async
  case await
  case reasync
  case `rethrows`
  case `throw`
  case `throws`
  case `try`

  init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
    switch lexeme {
    case TokenSpec(.asyncKeyword): self = .async
    case TokenSpec(.awaitKeyword, allowAtStartOfLine: false): self = .await
    case TokenSpec(.reasyncKeyword): self = .reasync
    case TokenSpec(.rethrowsKeyword): self = .rethrows
    case TokenSpec(.throwKeyword, allowAtStartOfLine: false): self = .throw
    case TokenSpec(.throwsKeyword): self = .throws
    case TokenSpec(.tryKeyword, allowAtStartOfLine: false): self = .try
    default: return nil
    }
  }

  var spec: TokenSpec {
    switch self {
    case .async: return .asyncKeyword
    case .await: return TokenSpec(.awaitKeyword, allowAtStartOfLine: false)
    case .reasync: return .reasyncKeyword
    case .rethrows: return .rethrowsKeyword
    case .throw: return TokenSpec(.throwKeyword, allowAtStartOfLine: false)
    case .throws: return .throwsKeyword
    case .try: return TokenSpec(.tryKeyword, allowAtStartOfLine: false)
    }
  }
}
