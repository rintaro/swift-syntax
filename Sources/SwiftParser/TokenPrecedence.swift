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

/// Describes how distinctive a token is for parser recovery.
///
/// When expecting a token, tokens with a lower token precedence may be skipped
/// and considered unexpected.
///
/// - Seealso: <doc:ParserRecovery>
enum TokenPrecedence: Comparable {
  /// An unknown token. This is known garbage and should always be allowed to be skipped.
  case unknownToken
  /// Tokens that can be used similar to variable names or literals
  case identifierLike
  /// Keywords and operators that can occur in the middle of an expression
  case exprKeyword
  /// A token that starts a bracketed expression which typically occurs inside
  /// a statement.
  case weakBracketed(closingDelimiter: RawTokenKind)
  /// A punctuator that can occur inside a statement
  case weakPunctuator
  /// A punctuator that is a fairly strong indicator of separating two distinct parts of a statement.
  case mediumPunctuator
  /// The closing delimiter of `weakBracketed`
  case weakBracketClose
  /// Keywords that start a new statement.
  case stmtKeyword
  /// The '{' token because it typically marks the body of a declaration.
  /// `closingDelimiter` must have type `strongPunctuator`
  case openingBrace(closingDelimiter: RawTokenKind)
  /// A punctuator that is a strong indicator that it separates two distinct parts of the source code, like two statements
  case strongPunctuator
  /// The closing delimiter of `strongBracketed`
  case closingBrace
  /// Tokens that start a new declaration
  case declKeyword
  case openingPoundIf
  case closingPoundIf

  /// If the precedence is `weakBracketed` or `strongBracketed`, the closing delimiter of the bracketed group.
  var closingTokenKind: RawTokenKind? {
    switch self {
    case .weakBracketed(closingDelimiter: let closingDelimiter):
      return closingDelimiter
    case .openingBrace(closingDelimiter: let closingDelimiter):
      return closingDelimiter
    case .openingPoundIf:
      return .poundEndif
    default:
      return nil
    }
  }

  static func < (lhs: TokenPrecedence, rhs: TokenPrecedence) -> Bool {
    func precedence(_ precedence: TokenPrecedence) -> Int {
      /// Should match the order of the cases in the enum.
      switch precedence {
      case .unknownToken:
        return 0
      case .identifierLike:
        return 1
      case .exprKeyword:
        return 2
      case .weakBracketed:
        return 3
      case .weakPunctuator:
        return 4
      case .mediumPunctuator:
        return 5
      case .weakBracketClose:
        return 6
      case .stmtKeyword:
        return 7
      case .strongPunctuator:
        return 8
      case .openingBrace:
        return 9
      case .closingBrace:
        return 10
      case .declKeyword:
        return 11
      case .openingPoundIf:
        return 12
      case .closingPoundIf:
        return 13
      }
    }

    return precedence(lhs) < precedence(rhs)
  }

  /// When expecting a token with `stmtKeyword` precedence or higher, newlines may be skipped to find that token.
  /// For lower precedence groups, we consider newlines the end of the lookahead scope.
  var shouldSkipOverNewlines: Bool {
    return self >= .stmtKeyword
  }

  init(_ lexeme: Lexer.Lexeme) {
    self.init(lexeme.rawTokenKind)
  }

  init(_ tokenKind: RawTokenKind) {
    switch tokenKind {
    case .unknown:
      self = .unknownToken
    // MARK: Identifier like
    case  // Literals
    .floatLiteral, .integerLiteral,
      // Pound literals
      .poundAvailable, .poundSourceLocation, .poundUnavailable,
      // Identifiers
      .dollarIdentifier, .identifier,
      // '_' can occur in types to replace a type identifier
      .wildcard,
      // String segment, string interpolation anchor, pound, shebang and regex pattern don't really fit anywhere else
      .pound, .stringSegment, .regexLiteralPattern, .shebang:
      self = .identifierLike

    // MARK: Expr keyword
    case  // Operators can occur inside expressions
    .postfixOperator, .prefixOperator, .binaryOperator:
      // Consider 'any' and 'inout' like a prefix operator to a type and a type is expression-like.
      self = .exprKeyword

    // MARK: Weak bracketed
    case .leftParen:
      self = .weakBracketed(closingDelimiter: .rightParen)
    case .leftSquare:
      self = .weakBracketed(closingDelimiter: .rightSquare)
    case .leftAngle:
      self = .weakBracketed(closingDelimiter: .rightAngle)
    case .multilineStringQuote, .rawStringPoundDelimiter, .singleQuote, .stringQuote,
      .regexSlash, .regexPoundDelimiter:
      self = .weakBracketed(closingDelimiter: tokenKind)
    case  // Chaining punctuators
    .infixQuestionMark, .period, .postfixQuestionMark, .exclamationMark,
      // Misc
      .backslash, .backtick, .ellipsis, .equal, .prefixAmpersand:
      self = .weakPunctuator

    case .atSign, .colon, .comma:
      self = .mediumPunctuator

    // MARK: Weak bracket close
    case  // Weak brackets
    .rightAngle, .rightParen, .rightSquare:
      self = .weakBracketClose

    // MARK: Strong bracketed
    case .leftBrace:
      self = .openingBrace(closingDelimiter: .rightBrace)
    case .poundElseif, .poundElse, .poundIf:
      self = .openingPoundIf

    // MARK: Strong punctuator
    case  // Semicolon separates two statements
    .semicolon,
      // Arrow is a strong indicator in a function type that we are now in the return type
      .arrow,
      // endOfFile is here because it is a very strong marker and doesn't belong anywhere else
      .endOfFile:
      self = .strongPunctuator

    // MARK: Strong bracket close
    case .rightBrace:
      self = .closingBrace
    case .poundEndif:
      self = .closingPoundIf

    // MARK: Identifier like
    case  // Literals
    .SelfKeyword, .falseKeyword, .nilKeyword, .selfKeyword, .superKeyword, .trueKeyword:
      self = .identifierLike

    // MARK: Expr keyword
    case  // Keywords
    .asKeyword, .isKeyword, .someKeyword, .tryKeyword,
      .awaitKeyword, .eachKeyword, .copyKeyword,
      // We don't know much about which contextual keyword it is, be conservative an allow considering it as unexpected.
      // Keywords in function types (we should be allowed to skip them inside parenthesis)
      .rethrowsKeyword, .throwsKeyword, .reasyncKeyword, .asyncKeyword,
      // Consider 'any' a prefix operator to a type and a type is expression-like.
      .AnyKeyword,
      // 'where' can only occur in the signature of declarations. Consider the signature expression-like.
      .whereKeyword,
      // 'in' occurs in closure input/output definitions and for loops. Consider both constructs expression-like.
      .inKeyword:
      self = .exprKeyword

    case  // Control-flow constructs
    .deferKeyword, .doKeyword, .forKeyword, .guardKeyword, .ifKeyword, .repeatKeyword, .switchKeyword, .whileKeyword,
      // Secondary parts of control-flow constructs
      .caseKeyword, .catchKeyword, .defaultKeyword, .elseKeyword,
      // Return-like statements
      .breakKeyword, .continueKeyword, .fallthroughKeyword, .returnKeyword, .throwKeyword, .thenKeyword, .yieldKeyword:
      self = .stmtKeyword

    // MARK: Decl keywords
    case  // Types
    .associatedtypeKeyword,
      .classKeyword,
      .enumKeyword,
      .extensionKeyword,
      .protocolKeyword,
      .structKeyword,
      .typealiasKeyword,
      .actorKeyword,
      .macroKeyword,

      // Access modifiers
      .fileprivateKeyword,
      .internalKeyword,
      .privateKeyword,
      .publicKeyword,
      .staticKeyword,

      // Functions
      .deinitKeyword,
      .funcKeyword,
      .initKeyword,
      .subscriptKeyword,

      // Variables
      .letKeyword,
      .varKeyword,

      // Operator stuff
      .operatorKeyword,
      .precedencegroupKeyword,

      // Declaration Modifiers
      .__consumingKeyword,
      .finalKeyword,
      .requiredKeyword,
      .optionalKeyword,
      .lazyKeyword,
      .dynamicKeyword,
      .infixKeyword,
      .postfixKeyword,
      .prefixKeyword,
      .mutatingKeyword,
      .nonmutatingKeyword,
      .convenienceKeyword,
      .overrideKeyword,
      .packageKeyword,
      .openKeyword,
      .__setter_accessKeyword,
      .indirectKeyword,
      .isolatedKeyword,
      .nonisolatedKeyword,
      .distributedKeyword,
      ._localKeyword,
      .inoutKeyword,
      ._mutatingKeyword,
      ._borrowKeyword,
      ._borrowingKeyword,
      .borrowingKeyword,
      ._consumingKeyword,
      .consumingKeyword,
      .consumeKeyword,
      ._resultDependsOnSelfKeyword,
      ._resultDependsOnKeyword,

      // Accessors
      .getKeyword,
      .setKeyword,
      .didSetKeyword,
      .willSetKeyword,
      .unsafeAddressKeyword,
      .addressWithOwnerKeyword,
      .addressWithNativeOwnerKeyword,
      .unsafeMutableAddressKeyword,
      .mutableAddressWithOwnerKeyword,
      .mutableAddressWithNativeOwnerKeyword,
      ._readKeyword,
      ._modifyKeyword,

      // Misc
      .importKeyword:
      self = .declKeyword

    case  // `TypeAttribute`
    ._noMetadataKeyword,
      ._opaqueReturnTypeOfKeyword,
      .autoclosureKeyword,
      .conventionKeyword,
      .differentiableKeyword,
      .escapingKeyword,
      .noDerivativeKeyword,
      .noescapeKeyword,
      .SendableKeyword,
      .retroactiveKeyword,
      .uncheckedKeyword:
      self = .exprKeyword

    case  // `DeclarationAttributeWithSpecialSyntax`
    ._alignmentKeyword,
      ._backDeployKeyword,
      ._cdeclKeyword,
      ._documentationKeyword,
      ._dynamicReplacementKeyword,
      ._effectsKeyword,
      ._exposeKeyword,
      ._implementsKeyword,
      ._nonSendableKeyword,
      ._objcImplementationKeyword,
      ._objcRuntimeNameKeyword,
      ._optimizeKeyword,
      ._originallyDefinedInKeyword,
      ._privateKeyword,
      ._projectedValuePropertyKeyword,
      ._semanticsKeyword,
      ._specializeKeyword,
      ._spiKeyword,
      ._spi_availableKeyword,
      ._swift_native_objc_runtime_baseKeyword,
      ._typeEraserKeyword,
      ._unavailableFromAsyncKeyword,
      .attachedKeyword,
      .availableKeyword,
      .backDeployedKeyword,
      .derivativeKeyword,
      .exclusivityKeyword,
      .inlineKeyword,
      .objcKeyword,
      .transposeKeyword:
      self = .exprKeyword

    case  // Treat all other keywords as expression keywords in the absence of any better information.
    .__ownedKeyword,
      .__sharedKeyword,
      ._BridgeObjectKeyword,
      ._ClassKeyword,
      ._compilerInitializedKeyword,
      ._constKeyword,
      ._forwardKeyword,
      ._linearKeyword,
      ._moveKeyword,
      ._NativeClassKeyword,
      ._NativeRefCountedObjectKeyword,
      ._PackageDescriptionKeyword,
      ._RefCountedObjectKeyword,
      ._TrivialKeyword,
      ._TrivialAtMostKeyword,
      ._TrivialStride,
      ._underlyingVersionKeyword,
      ._UnknownLayoutKeyword,
      ._versionKeyword,
      .accessesKeyword,
      .anyKeyword,
      .assignmentKeyword,
      .associativityKeyword,
      .availabilityKeyword,
      .beforeKeyword,
      .blockKeyword,
      .canImportKeyword,
      .compilerKeyword,
      .cTypeKeyword,
      .deprecatedKeyword,
      .exportedKeyword,
      .fileKeyword,
      .discardKeyword,
      .forwardKeyword,
      .higherThanKeyword,
      .initializesKeyword,
      .introducedKeyword,
      .kindKeyword,
      .leftKeyword,
      .lineKeyword,
      .linearKeyword,
      .lowerThanKeyword,
      .messageKeyword,
      .metadataKeyword,
      .moduleKeyword,
      .noasyncKeyword,
      .noneKeyword,
      .obsoletedKeyword,
      .ofKeyword,
      .ProtocolKeyword,
      .renamedKeyword,
      .reverseKeyword,
      .rightKeyword,
      .safeKeyword,
      .sourceFileKeyword,
      .spiKeyword,
      .spiModuleKeyword,
      .swiftKeyword,
      .targetKeyword,
      .TypeKeyword,
      .unavailableKeyword,
      .unownedKeyword,
      .visibilityKeyword,
      .weakKeyword,
      .witness_methodKeyword,
      .wrtKeyword,
      .unsafeKeyword:
      self = .exprKeyword
    }
  }
}
