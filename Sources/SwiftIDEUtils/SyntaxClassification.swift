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

@_spi(RawSyntax) import SwiftSyntax

public enum SyntaxClassification {
  /// An attribute starting with an `@`.
  case attribute
  /// A block comment starting with `/**` and ending with `*/.
  case blockComment
  /// A doc block comment starting with `/**` and ending with `*/.
  case docBlockComment
  /// A doc line comment starting with `///`.
  case docLineComment
  /// An identifier starting with `$` like `$0`.
  case dollarIdentifier
  /// An editor placeholder of the form `<#content#>`
  case editorPlaceholder
  /// A floating point literal.
  case floatLiteral
  /// A generic identifier.
  case identifier
  /// A directive starting with `#if`, `#elseif`or `#else`.
  case ifConfigDirective
  /// An integer literal.
  case integerLiteral
  /// A Swift keyword, including contextual keywords.
  case keyword
  /// A line comment starting with `//`.
  case lineComment
  /// The token should not receive syntax coloring.
  case none
  /// An identifier referring to an operator.
  case `operator`
  /// A regex literal, including multiline regex literals.
  case regexLiteral
  /// A string literal including multiline string literals.
  case stringLiteral
  /// An identifier referring to a type.
  case type
  /// The label of a function parameter or a function call argument.
  case argumentLabel
}

extension SyntaxClassification {
  /// Checks if a node has a classification attached via its syntax definition.
  /// - Parameters:
  ///   - parentKind: The parent node syntax kind.
  ///   - indexInParent: The index of the node in its parent.
  ///   - childKind: The node syntax kind.
  /// - Returns: A pair of classification and whether it is "forced", or nil if
  ///   no classification is attached.
  internal static func classify(_ keyPath: AnyKeyPath) -> (SyntaxClassification, Bool)? {
    switch keyPath {
    case \AttributeSyntax.attributeName:
      return (.attribute, true)
    case \PlatformVersionItemSyntax.platformVersion:
      return (.keyword, false)
    case \AvailabilityVersionRestrictionSyntax.platform:
      return (.keyword, false)
    case \DeclModifierSyntax.name:
      return (.attribute, false)
    case \IfConfigClauseSyntax.poundKeyword:
      return (.ifConfigDirective, false)
    case \IfConfigClauseSyntax.condition:
      return (.ifConfigDirective, false)
    case \IfConfigDeclSyntax.poundEndif:
      return (.ifConfigDirective, false)
    case \MemberTypeIdentifierSyntax.name:
      return (.type, false)
    case \OperatorDeclSyntax.name:
      return (.operator, false)
    case \PrecedenceGroupAssociativitySyntax.associativityLabel:
      return (.keyword, false)
    case \PrecedenceGroupRelationSyntax.higherThanOrLowerThanLabel:
      return (.keyword, false)
    case \SimpleTypeIdentifierSyntax.name:
      return (.type, false)
    case \FunctionParameterSyntax.firstName:
      return (.argumentLabel, false)
    case \LabeledExprSyntax.label:
      return (.argumentLabel, false)
    default:
      return nil
    }
  }
}

extension RawTokenKind {
  internal var classification: SyntaxClassification {
    switch self {
    case .arrow:
      return .none
    case .atSign:
      return .attribute
    case .backslash:
      return .none
    case .backtick:
      return .none
    case .binaryOperator:
      return .operator
    case .colon:
      return .none
    case .comma:
      return .none
    case .dollarIdentifier:
      return .dollarIdentifier
    case .ellipsis:
      return .none
    case .endOfFile:
      return .none
    case .equal:
      return .none
    case .exclamationMark:
      return .none
    case .floatLiteral:
      return .floatLiteral
    case .identifier:
      return .identifier
    case .infixQuestionMark:
      return .none
    case .integerLiteral:
      return .integerLiteral
    case .leftAngle:
      return .none
    case .leftBrace:
      return .none
    case .leftParen:
      return .none
    case .leftSquare:
      return .none
    case .multilineStringQuote:
      return .stringLiteral
    case .period:
      return .none
    case .postfixOperator:
      return .operator
    case .postfixQuestionMark:
      return .none
    case .pound:
      return .none
    case .poundAvailable:
      return .none
    case .poundElse:
      return .ifConfigDirective
    case .poundElseif:
      return .ifConfigDirective
    case .poundEndif:
      return .ifConfigDirective
    case .poundIf:
      return .ifConfigDirective
    case .poundSourceLocation:
      return .keyword
    case .poundUnavailable:
      return .none
    case .prefixAmpersand:
      return .none
    case .prefixOperator:
      return .operator
    case .rawStringPoundDelimiter:
      return .none
    case .regexLiteralPattern:
      return .regexLiteral
    case .regexPoundDelimiter:
      return .regexLiteral
    case .regexSlash:
      return .regexLiteral
    case .rightAngle:
      return .none
    case .rightBrace:
      return .none
    case .rightParen:
      return .none
    case .rightSquare:
      return .none
    case .semicolon:
      return .none
    case .shebang:
      return .none
    case .singleQuote:
      return .stringLiteral
    case .stringQuote:
      return .stringLiteral
    case .stringSegment:
      return .stringLiteral
    case .unknown:
      return .none
    case .wildcard:
      return .none
    case .__consumingKeyword:
      return .keyword
    case .__ownedKeyword:
      return .keyword
    case .__setter_accessKeyword:
      return .keyword
    case .__sharedKeyword:
      return .keyword
    case ._alignmentKeyword:
      return .keyword
    case ._backDeployKeyword:
      return .keyword
    case ._borrowKeyword:
      return .keyword
    case ._borrowingKeyword:
      return .keyword
    case ._cdeclKeyword:
      return .keyword
    case ._ClassKeyword:
      return .keyword
    case ._compilerInitializedKeyword:
      return .keyword
    case ._constKeyword:
      return .keyword
    case ._consumingKeyword:
      return .keyword
    case ._documentationKeyword:
      return .keyword
    case ._dynamicReplacementKeyword:
      return .keyword
    case ._effectsKeyword:
      return .keyword
    case ._exposeKeyword:
      return .keyword
    case ._forwardKeyword:
      return .keyword
    case ._implementsKeyword:
      return .keyword
    case ._linearKeyword:
      return .keyword
    case ._localKeyword:
      return .keyword
    case ._modifyKeyword:
      return .keyword
    case ._moveKeyword:
      return .keyword
    case ._mutatingKeyword:
      return .keyword
    case ._NativeClassKeyword:
      return .keyword
    case ._NativeRefCountedObjectKeyword:
      return .keyword
    case ._noMetadataKeyword:
      return .keyword
    case ._nonSendableKeyword:
      return .keyword
    case ._objcImplementationKeyword:
      return .keyword
    case ._objcRuntimeNameKeyword:
      return .keyword
    case ._opaqueReturnTypeOfKeyword:
      return .keyword
    case ._optimizeKeyword:
      return .keyword
    case ._originallyDefinedInKeyword:
      return .keyword
    case ._PackageDescriptionKeyword:
      return .keyword
    case ._privateKeyword:
      return .keyword
    case ._projectedValuePropertyKeyword:
      return .keyword
    case ._readKeyword:
      return .keyword
    case ._RefCountedObjectKeyword:
      return .keyword
    case ._semanticsKeyword:
      return .keyword
    case ._specializeKeyword:
      return .keyword
    case ._spiKeyword:
      return .keyword
    case ._spi_availableKeyword:
      return .keyword
    case ._swift_native_objc_runtime_baseKeyword:
      return .keyword
    case ._TrivialKeyword:
      return .keyword
    case ._TrivialAtMostKeyword:
      return .keyword
    case ._typeEraserKeyword:
      return .keyword
    case ._unavailableFromAsyncKeyword:
      return .keyword
    case ._underlyingVersionKeyword:
      return .keyword
    case ._UnknownLayoutKeyword:
      return .keyword
    case ._versionKeyword:
      return .keyword
    case .accessesKeyword:
      return .keyword
    case .actorKeyword:
      return .keyword
    case .addressWithNativeOwnerKeyword:
      return .keyword
    case .addressWithOwnerKeyword:
      return .keyword
    case .anyKeyword:
      return .keyword
    case .AnyKeyword:
      return .keyword
    case .asKeyword:
      return .keyword
    case .assignmentKeyword:
      return .keyword
    case .associatedtypeKeyword:
      return .keyword
    case .associativityKeyword:
      return .keyword
    case .asyncKeyword:
      return .keyword
    case .attachedKeyword:
      return .keyword
    case .autoclosureKeyword:
      return .keyword
    case .availabilityKeyword:
      return .keyword
    case .availableKeyword:
      return .keyword
    case .awaitKeyword:
      return .keyword
    case .backDeployedKeyword:
      return .keyword
    case .beforeKeyword:
      return .keyword
    case .blockKeyword:
      return .keyword
    case .borrowingKeyword:
      return .keyword
    case .breakKeyword:
      return .keyword
    case .canImportKeyword:
      return .keyword
    case .caseKeyword:
      return .keyword
    case .catchKeyword:
      return .keyword
    case .classKeyword:
      return .keyword
    case .compilerKeyword:
      return .keyword
    case .consumeKeyword:
      return .keyword
    case .copyKeyword:
      return .keyword
    case .consumingKeyword:
      return .keyword
    case .continueKeyword:
      return .keyword
    case .convenienceKeyword:
      return .keyword
    case .conventionKeyword:
      return .keyword
    case .cTypeKeyword:
      return .keyword
    case .defaultKeyword:
      return .keyword
    case .deferKeyword:
      return .keyword
    case .deinitKeyword:
      return .keyword
    case .deprecatedKeyword:
      return .keyword
    case .derivativeKeyword:
      return .keyword
    case .didSetKeyword:
      return .keyword
    case .differentiableKeyword:
      return .keyword
    case .distributedKeyword:
      return .keyword
    case .doKeyword:
      return .keyword
    case .dynamicKeyword:
      return .keyword
    case .eachKeyword:
      return .keyword
    case .elseKeyword:
      return .keyword
    case .enumKeyword:
      return .keyword
    case .escapingKeyword:
      return .keyword
    case .exclusivityKeyword:
      return .keyword
    case .exportedKeyword:
      return .keyword
    case .extensionKeyword:
      return .keyword
    case .fallthroughKeyword:
      return .keyword
    case .falseKeyword:
      return .keyword
    case .fileKeyword:
      return .keyword
    case .fileprivateKeyword:
      return .keyword
    case .finalKeyword:
      return .keyword
    case .forKeyword:
      return .keyword
    case .discardKeyword:
      return .keyword
    case .forwardKeyword:
      return .keyword
    case .funcKeyword:
      return .keyword
    case .getKeyword:
      return .keyword
    case .guardKeyword:
      return .keyword
    case .higherThanKeyword:
      return .keyword
    case .ifKeyword:
      return .keyword
    case .importKeyword:
      return .keyword
    case .inKeyword:
      return .keyword
    case .indirectKeyword:
      return .keyword
    case .infixKeyword:
      return .keyword
    case .initKeyword:
      return .keyword
    case .initializesKeyword:
      return .keyword
    case .inlineKeyword:
      return .keyword
    case .inoutKeyword:
      return .keyword
    case .internalKeyword:
      return .keyword
    case .introducedKeyword:
      return .keyword
    case .isKeyword:
      return .keyword
    case .isolatedKeyword:
      return .keyword
    case .kindKeyword:
      return .keyword
    case .lazyKeyword:
      return .keyword
    case .leftKeyword:
      return .keyword
    case .letKeyword:
      return .keyword
    case .lineKeyword:
      return .keyword
    case .linearKeyword:
      return .keyword
    case .lowerThanKeyword:
      return .keyword
    case .macroKeyword:
      return .keyword
    case .messageKeyword:
      return .keyword
    case .metadataKeyword:
      return .keyword
    case .moduleKeyword:
      return .keyword
    case .mutableAddressWithNativeOwnerKeyword:
      return .keyword
    case .mutableAddressWithOwnerKeyword:
      return .keyword
    case .mutatingKeyword:
      return .keyword
    case .nilKeyword:
      return .keyword
    case .noasyncKeyword:
      return .keyword
    case .noDerivativeKeyword:
      return .keyword
    case .noescapeKeyword:
      return .keyword
    case .noneKeyword:
      return .keyword
    case .nonisolatedKeyword:
      return .keyword
    case .nonmutatingKeyword:
      return .keyword
    case .objcKeyword:
      return .keyword
    case .obsoletedKeyword:
      return .keyword
    case .ofKeyword:
      return .keyword
    case .openKeyword:
      return .keyword
    case .operatorKeyword:
      return .keyword
    case .optionalKeyword:
      return .keyword
    case .overrideKeyword:
      return .keyword
    case .packageKeyword:
      return .keyword
    case .postfixKeyword:
      return .keyword
    case .precedencegroupKeyword:
      return .keyword
    case .prefixKeyword:
      return .keyword
    case .privateKeyword:
      return .keyword
    case .ProtocolKeyword:
      return .keyword
    case .protocolKeyword:
      return .keyword
    case .publicKeyword:
      return .keyword
    case .reasyncKeyword:
      return .keyword
    case .renamedKeyword:
      return .keyword
    case .repeatKeyword:
      return .keyword
    case .requiredKeyword:
      return .keyword
    case ._resultDependsOnKeyword:
      return .keyword
    case ._resultDependsOnSelfKeyword:
      return .keyword
    case .rethrowsKeyword:
      return .keyword
    case .retroactiveKeyword:
      return .keyword
    case .returnKeyword:
      return .keyword
    case .reverseKeyword:
      return .keyword
    case .rightKeyword:
      return .keyword
    case .safeKeyword:
      return .keyword
    case .selfKeyword:
      return .keyword
    case .SelfKeyword:
      return .keyword
    case .SendableKeyword:
      return .keyword
    case .setKeyword:
      return .keyword
    case .someKeyword:
      return .keyword
    case .sourceFileKeyword:
      return .keyword
    case .spiKeyword:
      return .keyword
    case .spiModuleKeyword:
      return .keyword
    case .staticKeyword:
      return .keyword
    case .structKeyword:
      return .keyword
    case .subscriptKeyword:
      return .keyword
    case .superKeyword:
      return .keyword
    case .swiftKeyword:
      return .keyword
    case .switchKeyword:
      return .keyword
    case .targetKeyword:
      return .keyword
    case .thenKeyword:
      return .keyword
    case .throwKeyword:
      return .keyword
    case .throwsKeyword:
      return .keyword
    case .transposeKeyword:
      return .keyword
    case .trueKeyword:
      return .keyword
    case .tryKeyword:
      return .keyword
    case .TypeKeyword:
      return .keyword
    case .typealiasKeyword:
      return .keyword
    case .unavailableKeyword:
      return .keyword
    case .uncheckedKeyword:
      return .keyword
    case .unownedKeyword:
      return .keyword
    case .unsafeKeyword:
      return .keyword
    case .unsafeAddressKeyword:
      return .keyword
    case .unsafeMutableAddressKeyword:
      return .keyword
    case .varKeyword:
      return .keyword
    case .visibilityKeyword:
      return .keyword
    case .weakKeyword:
      return .keyword
    case .whereKeyword:
      return .keyword
    case .whileKeyword:
      return .keyword
    case .willSetKeyword:
      return .keyword
    case .witness_methodKeyword:
      return .keyword
    case .wrtKeyword:
      return .keyword
    case .yieldKeyword:
      return .keyword
    }
  }
}
