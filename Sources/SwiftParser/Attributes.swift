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

extension Parser {
  mutating func parseAttributeList() -> RawAttributeListSyntax {
    guard self.at(.atSign, .poundIf) else {
      return self.emptyCollection(RawAttributeListSyntax.self)
    }

    var elements = [RawAttributeListSyntax.Element]()
    var loopProgress = LoopProgressCondition()
    repeat {
      let attribute = self.parseAttribute()
      elements.append(attribute)
    } while self.at(.atSign, .poundIf) && self.hasProgressed(&loopProgress)
    return RawAttributeListSyntax(elements: elements, arena: self.arena)
  }
}

extension Parser {
  /// Compiler-known attributes that take arguments.
  enum DeclarationAttributeWithSpecialSyntax: TokenSpecSet {
    case _alignment
    case _backDeploy
    case _cdecl
    case _documentation
    case _dynamicReplacement
    case _effects
    case _expose
    case _implements
    case _nonSendable
    case _objcImplementation
    case _objcRuntimeName
    case _optimize
    case _originallyDefinedIn
    case _private
    case _projectedValueProperty
    case _semantics
    case _specialize
    case _spi
    case _spi_available
    case _swift_native_objc_runtime_base
    case _typeEraser
    case _unavailableFromAsync
    case `rethrows`
    case attached
    case available
    case backDeployed
    case derivative
    case differentiable
    case exclusivity
    case inline
    case objc
    case Sendable
    case transpose

    init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
      switch lexeme {
      case TokenSpec(._alignmentKeyword): self = ._alignment
      case TokenSpec(._backDeployKeyword): self = ._backDeploy
      case TokenSpec(._cdeclKeyword): self = ._cdecl
      case TokenSpec(._documentationKeyword): self = ._documentation
      case TokenSpec(._dynamicReplacementKeyword): self = ._dynamicReplacement
      case TokenSpec(._effectsKeyword): self = ._effects
      case TokenSpec(._exposeKeyword): self = ._expose
      case TokenSpec(._implementsKeyword): self = ._implements
      case TokenSpec(._nonSendableKeyword): self = ._nonSendable
      case TokenSpec(._objcImplementationKeyword): self = ._objcImplementation
      case TokenSpec(._objcRuntimeNameKeyword): self = ._objcRuntimeName
      case TokenSpec(._optimizeKeyword): self = ._optimize
      case TokenSpec(._originallyDefinedInKeyword): self = ._originallyDefinedIn
      case TokenSpec(._privateKeyword): self = ._private
      case TokenSpec(._projectedValuePropertyKeyword): self = ._projectedValueProperty
      case TokenSpec(._semanticsKeyword): self = ._semantics
      case TokenSpec(._specializeKeyword): self = ._specialize
      case TokenSpec(._spiKeyword): self = ._spi
      case TokenSpec(._spi_availableKeyword): self = ._spi_available
      case TokenSpec(._swift_native_objc_runtime_baseKeyword): self = ._swift_native_objc_runtime_base
      case TokenSpec(._typeEraserKeyword): self = ._typeEraser
      case TokenSpec(._unavailableFromAsyncKeyword): self = ._unavailableFromAsync
      case TokenSpec(.rethrowsKeyword): self = .rethrows
      case TokenSpec(.attachedKeyword): self = .attached
      case TokenSpec(.availableKeyword): self = .available
      case TokenSpec(.backDeployedKeyword): self = .backDeployed
      case TokenSpec(.derivativeKeyword): self = .derivative
      case TokenSpec(.differentiableKeyword): self = .differentiable
      case TokenSpec(.exclusivityKeyword): self = .exclusivity
      case TokenSpec(.inlineKeyword): self = .inline
      case TokenSpec(.objcKeyword): self = .objc
      case TokenSpec(.SendableKeyword): self = .Sendable
      case TokenSpec(.transposeKeyword): self = .transpose
      default:
        return nil
      }
    }

    var spec: TokenSpec {
      switch self {
      case ._alignment: return ._alignmentKeyword
      case ._backDeploy: return ._backDeployKeyword
      case ._cdecl: return ._cdeclKeyword
      case ._documentation: return ._documentationKeyword
      case ._dynamicReplacement: return ._dynamicReplacementKeyword
      case ._effects: return ._effectsKeyword
      case ._expose: return ._exposeKeyword
      case ._implements: return ._implementsKeyword
      case ._nonSendable: return ._nonSendableKeyword
      case ._objcImplementation: return ._objcImplementationKeyword
      case ._objcRuntimeName: return ._objcRuntimeNameKeyword
      case ._optimize: return ._optimizeKeyword
      case ._originallyDefinedIn: return ._originallyDefinedInKeyword
      case ._private: return ._privateKeyword
      case ._projectedValueProperty: return ._projectedValuePropertyKeyword
      case ._semantics: return ._semanticsKeyword
      case ._specialize: return ._specializeKeyword
      case ._spi: return ._spiKeyword
      case ._spi_available: return ._spi_availableKeyword
      case ._swift_native_objc_runtime_base: return ._swift_native_objc_runtime_baseKeyword
      case ._typeEraser: return ._typeEraserKeyword
      case ._unavailableFromAsync: return ._unavailableFromAsyncKeyword
      case .`rethrows`: return .rethrowsKeyword
      case .attached: return .attachedKeyword
      case .available: return .availableKeyword
      case .backDeployed: return .backDeployedKeyword
      case .derivative: return .derivativeKeyword
      case .differentiable: return .differentiableKeyword
      case .exclusivity: return .exclusivityKeyword
      case .inline: return .inlineKeyword
      case .objc: return .objcKeyword
      case .Sendable: return .SendableKeyword
      case .transpose: return .transposeKeyword
      }
    }
  }
}

extension Parser {
  mutating func parseAttributeWithoutArguments() -> RawAttributeListSyntax.Element {
    let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
    let attributeName = self.parseType()
    return .attribute(
      RawAttributeSyntax(
        unexpectedBeforeAtSign,
        atSign: atSign,
        attributeName: attributeName,
        leftParen: nil,
        arguments: nil,
        rightParen: nil,
        arena: self.arena
      )
    )
  }

  enum AttributeArgumentMode {
    case required
    case customAttribute
    case optional
    case noArgument
  }

  mutating func parseAttribute(
    argumentMode: AttributeArgumentMode,
    parseArguments: (inout Parser) -> RawAttributeSyntax.Arguments
  ) -> RawAttributeListSyntax.Element {
    let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
    let attributeName = self.parseType()
    let shouldParseArgument: Bool
    switch argumentMode {
    case .required:
      shouldParseArgument = true
    case .customAttribute:
      shouldParseArgument = self.withLookahead { $0.atCustomAttributeArgument() } && self.at(TokenSpec(.leftParen, allowAtStartOfLine: false))
    case .optional:
      shouldParseArgument = self.at(.leftParen)
    case .noArgument:
      shouldParseArgument = false
    }
    if shouldParseArgument {
      let (unexpectedBeforeLeftParen, leftParen) = self.expect(.leftParen)
      let argument = parseArguments(&self)
      let (unexpectedBeforeRightParen, rightParen) = self.expect(.rightParen)
      return .attribute(
        RawAttributeSyntax(
          unexpectedBeforeAtSign,
          atSign: atSign,
          attributeName: attributeName,
          unexpectedBeforeLeftParen,
          leftParen: leftParen,
          arguments: argument,
          unexpectedBeforeRightParen,
          rightParen: rightParen,
          arena: self.arena
        )
      )
    } else {
      return .attribute(
        RawAttributeSyntax(
          unexpectedBeforeAtSign,
          atSign: atSign,
          attributeName: attributeName,
          leftParen: nil,
          arguments: nil,
          rightParen: nil,
          arena: self.arena
        )
      )
    }
  }

  mutating func parseAttribute() -> RawAttributeListSyntax.Element {
    if self.at(.poundIf) {
      return .ifConfigDecl(
        self.parsePoundIfDirective { (parser, _) -> RawAttributeListSyntax.Element in
          return parser.parseAttribute()
        } syntax: { parser, attributes in
          return .attributes(RawAttributeListSyntax(elements: attributes, arena: parser.arena))
        }
      )
    }

    switch peek(isAtAnyIn: DeclarationAttributeWithSpecialSyntax.self) {
    case .available, ._spi_available:
      return parseAttribute(argumentMode: .required) { parser in
        return .availability(parser.parseAvailabilityArgumentSpecList())
      }
    case .backDeployed, ._backDeploy:
      return parseAttribute(argumentMode: .required) { parser in
        return .backDeployedArguments(parser.parseBackDeployedAttributeArguments())
      }
    case .differentiable:
      return parseAttribute(argumentMode: .required) { parser in
        return .differentiableArguments(parser.parseDifferentiableAttributeArguments())
      }
    case .derivative, .transpose:
      return parseAttribute(argumentMode: .required) { parser in
        return .derivativeRegistrationArguments(parser.parseDerivativeAttributeArguments())
      }
    case .objc:
      return parseAttribute(argumentMode: .optional) { parser in
        return .objCName(parser.parseObjectiveCSelector())
      }
    case ._specialize:
      return parseAttribute(argumentMode: .required) { parser in
        return .specializeArguments(parser.parseSpecializeAttributeArgumentList())
      }
    case ._private:
      return parseAttribute(argumentMode: .required) { parser in
        return .underscorePrivateAttributeArguments(parser.parseUnderscorePrivateAttributeArguments())
      }
    case ._dynamicReplacement:
      return parseAttribute(argumentMode: .required) { parser in
        return .dynamicReplacementArguments(parser.parseDynamicReplacementAttributeArguments())
      }
    case ._documentation:
      return parseAttribute(argumentMode: .required) { parser in
        return .documentationArguments(parser.parseDocumentationAttributeArguments())
      }
    case ._spi, ._objcRuntimeName, ._projectedValueProperty, ._swift_native_objc_runtime_base, ._typeEraser, ._optimize, .exclusivity, .inline, ._alignment:
      // Attributes that take a single token as argument. Some examples of these include:
      //  - Arbitrary identifiers (e.g. `@_spi(RawSyntax)`)
      //  - An integer literal (e.g. `@_alignment(4)`)
      //
      //  Because there seem to be very little restrictions on these parameters (they could be keywords instead of identifiers), we just allow any token.
      return parseAttribute(argumentMode: .required) { parser in
        if !parser.at(.rightParen) {
          return .token(parser.consumeAnyToken())
        } else {
          return .token(parser.missingToken(.identifier))
        }
      }
    case ._objcImplementation, ._nonSendable:
      // Similar to the above but the argument is optional
      return parseAttribute(argumentMode: .optional) { parser in
        if !parser.at(.rightParen) {
          return .token(parser.consumeAnyToken())
        } else {
          return .token(parser.missingToken(.identifier))
        }
      }
    case ._effects:
      return parseAttribute(argumentMode: .required) { parser in
        // The contents of the @_effects attribute are parsed in SIL, we just
        // represent the contents as a list of tokens in SwiftSyntax.
        var tokens: [RawTokenSyntax] = []
        while !parser.at(.rightParen, .endOfFile) {
          tokens.append(parser.consumeAnyToken())
        }
        return .effectsArguments(RawEffectsAttributeArgumentListSyntax(elements: tokens, arena: parser.arena))
      }
    case ._cdecl:
      return parseAttribute(argumentMode: .required) { parser in
        return .string(parser.parseStringLiteral())
      }
    case ._implements:
      return parseAttribute(argumentMode: .required) { parser in
        return .implementsArguments(parser.parseImplementsAttributeArguments())
      }
    case ._semantics:
      return parseAttribute(argumentMode: .required) { parser in
        return .string(parser.parseStringLiteral())
      }
    case ._expose:
      return parseAttribute(argumentMode: .required) { parser in
        return .exposeAttributeArguments(parser.parseExposeArguments())
      }
    case ._originallyDefinedIn:
      return parseAttribute(argumentMode: .required) { parser in
        return .originallyDefinedInArguments(parser.parseOriginallyDefinedInAttributeArguments())
      }
    case ._unavailableFromAsync:
      return parseAttribute(argumentMode: .optional) { parser in
        return .unavailableFromAsyncArguments(parser.parseUnavailableFromAsyncAttributeArguments())
      }
    case .attached:
      return parseAttribute(argumentMode: .customAttribute) { parser in
        let arguments = parser.parseAttachedArguments()
        return .argumentList(RawLabeledExprListSyntax(elements: arguments, arena: parser.arena))
      }
    case .rethrows:
      let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
      let (unexpectedBeforeAttributeName, attributeName) = self.expect(TokenSpec(.rethrowsKeyword, remapping: .identifier))
      return .attribute(
        RawAttributeSyntax(
          unexpectedBeforeAtSign,
          atSign: atSign,
          unexpectedBeforeAttributeName,
          attributeName: RawTypeSyntax(RawIdentifierTypeSyntax(name: attributeName, genericArgumentClause: nil, arena: self.arena)),
          leftParen: nil,
          arguments: nil,
          rightParen: nil,
          arena: self.arena
        )
      )
    case .Sendable:
      return parseAttribute(argumentMode: .noArgument) { parser in
        preconditionFailure("Sendable has no argument")
      }
    case nil:
      return parseAttribute(argumentMode: .customAttribute) { parser in
        let arguments = parser.parseArgumentListElements(pattern: .none)
        return .argumentList(RawLabeledExprListSyntax(elements: arguments, arena: parser.arena))
      }
    }
  }
}

extension Parser {
  mutating func parseAttachedArguments() -> [RawLabeledExprSyntax] {
    let (unexpectedBeforeRole, role) = self.expect(.identifier, TokenSpec(.extensionKeyword, remapping: .identifier), default: .identifier)
    let roleTrailingComma = self.consume(if: .comma)
    let roleElement = RawLabeledExprSyntax(
      label: nil,
      colon: nil,
      expression: RawExprSyntax(
        RawDeclReferenceExprSyntax(
          unexpectedBeforeRole,
          baseName: role,
          argumentNames: nil,
          arena: self.arena
        )
      ),
      trailingComma: roleTrailingComma,
      arena: self.arena
    )
    let additionalArgs = self.parseArgumentListElements(pattern: .none)
    return [roleElement] + additionalArgs
  }
}

extension Parser {
  mutating func parseDifferentiableAttribute() -> RawAttributeSyntax {
    let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
    let (unexpectedBeforeDifferentiable, differentiable) = self.expect(TokenSpec(.differentiableKeyword, remapping: .identifier))
    let (unexpectedBeforeLeftParen, leftParen) = self.expect(.leftParen)

    let argument = self.parseDifferentiableAttributeArguments()
    let (unexpectedBeforeRightParen, rightParen) = self.expect(.rightParen)

    return RawAttributeSyntax(
      unexpectedBeforeAtSign,
      atSign: atSign,
      unexpectedBeforeDifferentiable,
      attributeName: RawTypeSyntax(RawIdentifierTypeSyntax(name: differentiable, genericArgumentClause: nil, arena: self.arena)),
      unexpectedBeforeLeftParen,
      leftParen: leftParen,
      arguments: .differentiableArguments(argument),
      unexpectedBeforeRightParen,
      rightParen: rightParen,
      arena: self.arena
    )
  }

  mutating func parseDifferentiableAttributeArguments() -> RawDifferentiableAttributeArgumentsSyntax {
    let kindSpecifier: RawTokenSyntax?
    let kindSpecifierComma: RawTokenSyntax?
    if let (_, handle) = self.at(anyIn: DifferentiableAttributeArgumentsSyntax.KindSpecifierOptions.self) {
      kindSpecifier = self.eat(handle)
      kindSpecifierComma = self.consume(if: .comma)
    } else {
      kindSpecifier = nil
      kindSpecifierComma = nil
    }

    let arguments: RawDifferentiabilityWithRespectToArgumentSyntax?
    let argumentsComma: RawTokenSyntax?
    if self.at(.wrtKeyword) {
      arguments = self.parseDifferentiabilityWithRespectToArgument()
      argumentsComma = self.consume(if: .comma)
    } else {
      arguments = nil
      argumentsComma = nil
    }

    let whereClause: RawGenericWhereClauseSyntax?
    if self.at(.whereKeyword) {
      whereClause = self.parseGenericWhereClause()
    } else {
      whereClause = nil
    }
    return RawDifferentiableAttributeArgumentsSyntax(
      kindSpecifier: kindSpecifier,
      kindSpecifierComma: kindSpecifierComma,
      arguments: arguments,
      argumentsComma: argumentsComma,
      genericWhereClause: whereClause,
      arena: self.arena
    )
  }

  mutating func parseDifferentiabilityWithRespectToArgument() -> RawDifferentiabilityWithRespectToArgumentSyntax {
    let (unexpectedBeforeWrt, wrt) = self.expect(.wrtKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)

    guard let leftParen = self.consume(if: .leftParen) else {
      // If no opening '(' for parameter list, parse a single parameter.
      let argument =
        self.parseDifferentiabilityArgument()
        ?? RawDifferentiabilityArgumentSyntax(
          argument: missingToken(.identifier),
          trailingComma: nil,
          arena: self.arena
        )
      return RawDifferentiabilityWithRespectToArgumentSyntax(
        unexpectedBeforeWrt,
        wrtLabel: wrt,
        unexpectedBeforeColon,
        colon: colon,
        arguments: .argument(argument),
        arena: self.arena
      )
    }

    var elements = [RawDifferentiabilityArgumentSyntax]()
    var loopProgress = LoopProgressCondition()
    while !self.at(.endOfFile, .rightParen) && self.hasProgressed(&loopProgress) {
      guard let param = self.parseDifferentiabilityArgument() else {
        break
      }
      elements.append(param)
    }
    let (unexpectedBeforeRightParen, rightParen) = self.expect(.rightParen)

    let arguments = RawDifferentiabilityArgumentListSyntax(elements: elements, arena: self.arena)
    let list = RawDifferentiabilityArgumentsSyntax(
      leftParen: leftParen,
      arguments: arguments,
      unexpectedBeforeRightParen,
      rightParen: rightParen,
      arena: self.arena
    )
    return RawDifferentiabilityWithRespectToArgumentSyntax(
      wrtLabel: wrt,
      unexpectedBeforeColon,
      colon: colon,
      arguments: .argumentList(list),
      arena: self.arena
    )
  }

  mutating func parseDifferentiabilityArgument() -> RawDifferentiabilityArgumentSyntax? {
    switch self.at(anyIn: DifferentiabilityArgumentSyntax.ArgumentOptions.self) {
    case (.identifier, let handle)?:
      let token = self.eat(handle)
      let comma = self.consume(if: .comma)
      return RawDifferentiabilityArgumentSyntax(
        argument: token,
        trailingComma: comma,
        arena: self.arena
      )
    case (.integerLiteral, let handle)?:
      let token = self.eat(handle)
      let comma = self.consume(if: .comma)
      return RawDifferentiabilityArgumentSyntax(
        argument: token,
        trailingComma: comma,
        arena: self.arena
      )
    case (.self, let handle)?:
      let token = self.eat(handle)
      let comma = self.consume(if: .comma)
      return RawDifferentiabilityArgumentSyntax(
        argument: token,
        trailingComma: comma,
        arena: self.arena
      )
    case nil:
      return nil
    }
  }
}

extension Parser {
  mutating func parseDerivativeAttribute() -> RawAttributeSyntax {
    let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
    let (unexpectedBeforeDerivative, derivative) = self.expect(TokenSpec(.derivativeKeyword, remapping: .identifier))

    let (unexpectedBeforeLeftParen, leftParen) = self.expect(.leftParen)
    let argument = self.parseDerivativeAttributeArguments()
    let (unexpectedBeforeRightParen, rightParen) = self.expect(.rightParen)

    return RawAttributeSyntax(
      unexpectedBeforeAtSign,
      atSign: atSign,
      unexpectedBeforeDerivative,
      attributeName: RawTypeSyntax(RawIdentifierTypeSyntax(name: derivative, genericArgumentClause: nil, arena: self.arena)),
      unexpectedBeforeLeftParen,
      leftParen: leftParen,
      arguments: .derivativeRegistrationArguments(argument),
      unexpectedBeforeRightParen,
      rightParen: rightParen,
      arena: self.arena
    )
  }

  mutating func parseTransposeAttribute() -> RawAttributeSyntax {
    let (unexpectedBeforeAtSign, atSign) = self.expect(.atSign)
    let (unexpectedBeforeTranspose, transpose) = self.expect(TokenSpec(.transposeKeyword, remapping: .identifier))

    let (unexpectedBeforeLeftParen, leftParen) = self.expect(.leftParen)
    let argument = self.parseDerivativeAttributeArguments()
    let (unexpectedBeforeRightParen, rightParen) = self.expect(.rightParen)

    return RawAttributeSyntax(
      unexpectedBeforeAtSign,
      atSign: atSign,
      unexpectedBeforeTranspose,
      attributeName: RawTypeSyntax(RawIdentifierTypeSyntax(name: transpose, genericArgumentClause: nil, arena: self.arena)),
      unexpectedBeforeLeftParen,
      leftParen: leftParen,
      arguments: .derivativeRegistrationArguments(argument),
      unexpectedBeforeRightParen,
      rightParen: rightParen,
      arena: self.arena
    )
  }

  mutating func parseDerivativeAttributeArguments() -> RawDerivativeAttributeArgumentsSyntax {
    let (unexpectedBeforeOfLabel, ofLabel) = self.expect(.ofKeyword)
    let (unexpectedBetweenOfLabelAndColon, colon) = self.expect(.colon)
    let originalDeclName = self.parseQualifiedDeclarationName()
    let period = self.consume(if: .period)
    let unexpectedBeforeAccessor: RawUnexpectedNodesSyntax?
    let accessor: RawTokenSyntax?
    if period != nil {
      (unexpectedBeforeAccessor, accessor) = self.expect(.getKeyword, .setKeyword, default: .getKeyword)
    } else {
      (unexpectedBeforeAccessor, accessor) = (nil, nil)
    }
    let comma = self.consume(if: .comma)
    let arguments: RawDifferentiabilityWithRespectToArgumentSyntax?
    if comma != nil {
      arguments = self.parseDifferentiabilityWithRespectToArgument()
    } else {
      arguments = nil
    }
    return RawDerivativeAttributeArgumentsSyntax(
      unexpectedBeforeOfLabel,
      ofLabel: ofLabel,
      unexpectedBetweenOfLabelAndColon,
      colon: colon,
      originalDeclName: originalDeclName,
      period: period,
      unexpectedBeforeAccessor,
      accessorSpecifier: accessor,
      comma: comma,
      arguments: arguments,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseObjectiveCSelector() -> RawObjCSelectorPieceListSyntax {
    var elements = [RawObjCSelectorPieceSyntax]()
    var loopProgress = LoopProgressCondition()
    while self.hasProgressed(&loopProgress) {
      // Empty selector piece.
      if let colon = self.consume(if: .colon) {
        elements.append(
          RawObjCSelectorPieceSyntax(
            name: nil,
            colon: colon,
            arena: self.arena
          )
        )
        continue
      } else if self.at(.identifier, .wildcard) || self.currentToken.isLexerClassifiedKeyword {
        let name = self.consumeAnyToken(remapping: .identifier)

        // If we hit a ')' we may have a zero-argument selector.
        if self.at(.rightParen) && elements.isEmpty {
          elements.append(
            RawObjCSelectorPieceSyntax(
              name: name,
              colon: nil,
              arena: self.arena
            )
          )
          break
        }

        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        elements.append(
          RawObjCSelectorPieceSyntax(
            name: name,
            unexpectedBeforeColon,
            colon: colon,
            arena: self.arena
          )
        )
      } else {
        break
      }
    }
    return RawObjCSelectorPieceListSyntax(elements: elements, arena: self.arena)
  }
}

extension Parser {
  mutating func parseSpecializeAttributeArgumentList() -> RawSpecializeAttributeArgumentListSyntax {
    var elements = [RawSpecializeAttributeArgumentListSyntax.Element]()
    // Parse optional "exported" and "kind" labeled parameters.
    var loopProgress = LoopProgressCondition()
    LOOP: while !self.at(.endOfFile, .rightParen, .whereKeyword) && self.hasProgressed(&loopProgress) {
      switch self.at(anyIn: LabeledSpecializeArgumentSyntax.LabelOptions.self) {
      case (.target, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        let declName = self.parseDeclReferenceExpr([.zeroArgCompoundNames, .keywordsUsingSpecialNames, .operators])
        let comma = self.consume(if: .comma)
        elements.append(
          .specializeTargetFunctionArgument(
            RawSpecializeTargetFunctionArgumentSyntax(
              targetLabel: label,
              unexpectedBeforeColon,
              colon: colon,
              declName: declName,
              trailingComma: comma,
              arena: self.arena
            )
          )
        )
      case (.availability, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        let availability = self.parseAvailabilitySpecList()
        let (unexpectedBeforeSemi, semi) = self.expect(.semicolon)
        elements.append(
          .specializeAvailabilityArgument(
            RawSpecializeAvailabilityArgumentSyntax(
              availabilityLabel: label,
              unexpectedBeforeColon,
              colon: colon,
              availabilityArguments: availability,
              unexpectedBeforeSemi,
              semicolon: semi,
              arena: self.arena
            )
          )
        )
      case (.available, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        // FIXME: I have no idea what this is supposed to be, but the Syntax
        // tree only allows us to insert a token so we'll take anything.
        let available = self.consumeAnyToken()
        let comma = self.consume(if: .comma)
        elements.append(
          .labeledSpecializeArgument(
            RawLabeledSpecializeArgumentSyntax(
              label: label,
              unexpectedBeforeColon,
              colon: colon,
              value: available,
              trailingComma: comma,
              arena: self.arena
            )
          )
        )
      case (.exported, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        let (unexpectedBeforeValue, value) = self.expect(.trueKeyword, .falseKeyword, default: .falseKeyword)
        let comma = self.consume(if: .comma)
        elements.append(
          .labeledSpecializeArgument(
            RawLabeledSpecializeArgumentSyntax(
              label: label,
              unexpectedBeforeColon,
              colon: colon,
              unexpectedBeforeValue,
              value: value,
              trailingComma: comma,
              arena: self.arena
            )
          )
        )
      case (.kind, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        let valueLabel = self.parseAnyIdentifier()
        let comma = self.consume(if: .comma)
        elements.append(
          .labeledSpecializeArgument(
            RawLabeledSpecializeArgumentSyntax(
              label: label,
              unexpectedBeforeColon,
              colon: colon,
              value: valueLabel,
              trailingComma: comma,
              arena: self.arena
            )
          )
        )
      case (.spiModule, let handle)?,
        (.spi, let handle)?:
        let label = self.eat(handle)
        let (unexpectedBeforeColon, colon) = self.expect(.colon)
        let valueLabel = self.consumeAnyToken()
        let comma = self.consume(if: .comma)
        elements.append(
          .labeledSpecializeArgument(
            RawLabeledSpecializeArgumentSyntax(
              label: label,
              unexpectedBeforeColon,
              colon: colon,
              value: valueLabel,
              trailingComma: comma,
              arena: self.arena
            )
          )
        )
      case nil:
        break LOOP
      }
    }

    // Parse the where clause.
    if self.at(.whereKeyword) {
      let whereClause = self.parseGenericWhereClause()
      elements.append(.genericWhereClause(whereClause))
    }
    return RawSpecializeAttributeArgumentListSyntax(elements: elements, arena: self.arena)
  }
}

extension Parser {
  mutating func parseImplementsAttributeArguments() -> RawImplementsAttributeArgumentsSyntax {
    let type = self.parseType()
    let (unexpectedBeforeComma, comma) = self.expect(.comma)
    let declName = self.parseDeclReferenceExpr([
      .zeroArgCompoundNames,
      .operators,
    ])
    return RawImplementsAttributeArgumentsSyntax(
      type: type,
      unexpectedBeforeComma,
      comma: comma,
      declName: declName,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseOpaqueReturnTypeOfAttributeArguments() -> RawOpaqueReturnTypeOfAttributeArgumentsSyntax {
    let mangledName = self.parseStringLiteral()
    let (unexpectedBeforeComma, comma) = self.expect(.comma)
    let (unexpectedBeforeOrdinal, ordinal) = self.expect(.integerLiteral)
    return RawOpaqueReturnTypeOfAttributeArgumentsSyntax(
      mangledName: mangledName,
      unexpectedBeforeComma,
      comma: comma,
      unexpectedBeforeOrdinal,
      ordinal: ordinal,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseConventionArguments() -> RawAttributeSyntax.Arguments {
    if let witnessMethod = self.consume(if: .witness_methodKeyword) {
      let (unexpectedBeforeColon, colon) = self.expect(.colon)
      let name = self.parseAnyIdentifier()
      return .conventionWitnessMethodArguments(
        RawConventionWitnessMethodAttributeArgumentsSyntax(
          witnessMethodLabel: witnessMethod,
          unexpectedBeforeColon,
          colon: colon,
          protocolName: name,
          arena: self.arena
        )
      )
    } else {
      let (unexpectedBeforeLabel, label) = self.expect(.identifier)
      let unexpectedBeforeComma: RawUnexpectedNodesSyntax?
      let comma: RawTokenSyntax?
      let unexpectedBeforeCTypeLabel: RawUnexpectedNodesSyntax?
      let cTypeLabel: RawTokenSyntax?
      let unexpectedBeforeColon: RawUnexpectedNodesSyntax?
      let colon: RawTokenSyntax?
      let cTypeString: RawStringLiteralExprSyntax?
      if self.at(.comma) {
        (unexpectedBeforeComma, comma) = self.expect(.comma)
        (unexpectedBeforeCTypeLabel, cTypeLabel) = self.expect(.cTypeKeyword)
        (unexpectedBeforeColon, colon) = self.expect(.colon)
        cTypeString = self.parseStringLiteral()
      } else {
        unexpectedBeforeComma = nil
        comma = nil
        unexpectedBeforeCTypeLabel = nil
        cTypeLabel = nil
        unexpectedBeforeColon = nil
        colon = nil
        cTypeString = nil
      }
      return .conventionArguments(
        RawConventionAttributeArgumentsSyntax(
          unexpectedBeforeLabel,
          conventionLabel: label,
          unexpectedBeforeComma,
          comma: comma,
          unexpectedBeforeCTypeLabel,
          cTypeLabel: cTypeLabel,
          unexpectedBeforeColon,
          colon: colon,
          cTypeString: cTypeString,
          arena: self.arena
        )
      )
    }
  }
}

extension Parser {
  mutating func parseBackDeployedAttributeArguments() -> RawBackDeployedAttributeArgumentsSyntax {
    let (unexpectedBeforeLabel, label) = self.expect(.beforeKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)
    var elements: [RawPlatformVersionItemSyntax] = []
    var keepGoing: RawTokenSyntax? = nil
    repeat {
      let versionRestriction = self.parsePlatformVersion()
      keepGoing = self.consume(if: .comma)
      elements.append(
        RawPlatformVersionItemSyntax(
          platformVersion: versionRestriction,
          trailingComma: keepGoing,
          arena: self.arena
        )
      )
    } while keepGoing != nil
    return RawBackDeployedAttributeArgumentsSyntax(
      unexpectedBeforeLabel,
      beforeLabel: label,
      unexpectedBeforeColon,
      colon: colon,
      platforms: RawPlatformVersionItemListSyntax(elements: elements, arena: self.arena),
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseExposeArguments() -> RawExposeAttributeArgumentsSyntax {
    let language: RawTokenSyntax
    if !self.at(.rightParen, .comma) {
      language = self.consumeAnyToken()
    } else {
      language = missingToken(.identifier)
    }
    let unexpectedBeforeComma: RawUnexpectedNodesSyntax?
    let comma: RawTokenSyntax?
    let cxxName: RawStringLiteralExprSyntax?
    if self.at(.comma) {
      (unexpectedBeforeComma, comma) = self.expect(.comma)
      cxxName = self.parseStringLiteral()
    } else {
      unexpectedBeforeComma = nil
      comma = nil
      cxxName = nil
    }
    return RawExposeAttributeArgumentsSyntax(
      language: language,
      unexpectedBeforeComma,
      comma: comma,
      cxxName: cxxName,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseOriginallyDefinedInAttributeArguments() -> RawOriginallyDefinedInAttributeArgumentsSyntax {
    let (unexpectedBeforeModuleLabel, moduleLabel) = self.expect(.moduleKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)
    let moduleName = self.parseStringLiteral()
    let (unexpectedBeforeComma, comma) = self.expect(.comma)

    var platforms: [RawPlatformVersionItemSyntax] = []
    var keepGoing: RawTokenSyntax?
    repeat {
      let restriction = self.parsePlatformVersion(allowStarAsVersionNumber: true)
      keepGoing = self.consume(if: .comma)
      platforms.append(
        RawPlatformVersionItemSyntax(
          platformVersion: restriction,
          trailingComma: keepGoing,
          arena: self.arena
        )
      )
    } while keepGoing != nil

    return RawOriginallyDefinedInAttributeArgumentsSyntax(
      unexpectedBeforeModuleLabel,
      moduleLabel: moduleLabel,
      unexpectedBeforeColon,
      colon: colon,
      moduleName: moduleName,
      unexpectedBeforeComma,
      comma: comma,
      platforms: RawPlatformVersionItemListSyntax(elements: platforms, arena: self.arena),
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseUnderscorePrivateAttributeArguments() -> RawUnderscorePrivateAttributeArgumentsSyntax {
    let (unexpectedBeforeLabel, label) = self.expect(.sourceFileKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)
    let filename = self.parseStringLiteral()
    return RawUnderscorePrivateAttributeArgumentsSyntax(
      unexpectedBeforeLabel,
      sourceFileLabel: label,
      unexpectedBeforeColon,
      colon: colon,
      filename: filename,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseDynamicReplacementAttributeArguments() -> RawDynamicReplacementAttributeArgumentsSyntax {
    let (unexpectedBeforeLabel, label) = self.expect(.forKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)
    let declName: RawDeclReferenceExprSyntax
    if label.isMissing && colon.isMissing && self.atStartOfLine {
      declName = RawDeclReferenceExprSyntax(
        baseName: RawTokenSyntax(missing: .identifier, arena: self.arena),
        argumentNames: nil,
        arena: self.arena
      )
    } else {
      declName = self.parseDeclReferenceExpr([
        .zeroArgCompoundNames, .keywordsUsingSpecialNames, .operators,
      ])
    }
    return RawDynamicReplacementAttributeArgumentsSyntax(
      unexpectedBeforeLabel,
      forLabel: label,
      unexpectedBeforeColon,
      colon: colon,
      declName: declName,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseUnavailableFromAsyncAttributeArguments() -> RawUnavailableFromAsyncAttributeArgumentsSyntax {
    let (unexpectedBeforeLabel, label) = self.expect(.messageKeyword)
    let (unexpectedBeforeColon, colon) = self.expect(.colon)

    let unexpectedBetweenColonAndMessage: RawUnexpectedNodesSyntax?
    if let equalToken = self.consume(if: .equal) {
      unexpectedBetweenColonAndMessage = RawUnexpectedNodesSyntax([equalToken], arena: self.arena)
    } else {
      unexpectedBetweenColonAndMessage = nil
    }

    let message = self.parseStringLiteral()
    return RawUnavailableFromAsyncAttributeArgumentsSyntax(
      unexpectedBeforeLabel,
      messageLabel: label,
      unexpectedBeforeColon,
      colon: colon,
      unexpectedBetweenColonAndMessage,
      message: message,
      arena: self.arena
    )
  }
}

extension Parser {
  mutating func parseDocumentationAttributeArguments() -> RawDocumentationAttributeArgumentListSyntax {
    var arguments: [RawDocumentationAttributeArgumentSyntax] = []

    var keepGoing: RawTokenSyntax? = nil
    repeat {
      let (unexpectedBeforeLabel, label) = self.expect(.visibilityKeyword, .metadataKeyword, default: .visibilityKeyword)
      let (unexpectedBeforeColon, colon) = self.expect(.colon)
      let unexpectedBeforeValue: RawUnexpectedNodesSyntax?
      let value: RawDocumentationAttributeArgumentSyntax.Value
      switch label.tokenText {
      case "visibility":
        enum AccessLevelModifier: TokenSpecSet {
          case `private`
          case `fileprivate`
          case `internal`
          case `public`
          case `open`

          var spec: TokenSpec {
            switch self {
            case .private: return .privateKeyword
            case .fileprivate: return .fileprivateKeyword
            case .internal: return .internalKeyword
            case .public: return .publicKeyword
            case .open: return .openKeyword
            }
          }

          init?(lexeme: Lexer.Lexeme, experimentalFeatures: Parser.ExperimentalFeatures) {
            switch lexeme {
            case TokenSpec(.privateKeyword): self = .private
            case TokenSpec(.fileprivateKeyword): self = .fileprivate
            case TokenSpec(.internalKeyword): self = .internal
            case TokenSpec(.publicKeyword): self = .public
            case TokenSpec(.openKeyword): self = .open
            default: return nil
            }
          }
        }

        let (unexpected, token) = self.expect(anyIn: AccessLevelModifier.self, default: .internal)
        unexpectedBeforeValue = unexpected
        value = .token(token)
      case "metadata":
        unexpectedBeforeValue = nil
        if let identifier = self.consume(if: .identifier) {
          value = .token(identifier)
        } else {
          value = .string(self.parseStringLiteral())
        }
      default:
        unexpectedBeforeValue = nil
        value = .token(missingToken(.identifier))
      }
      keepGoing = self.consume(if: .comma)
      arguments.append(
        RawDocumentationAttributeArgumentSyntax(
          unexpectedBeforeLabel,
          label: label,
          unexpectedBeforeColon,
          colon: colon,
          unexpectedBeforeValue,
          value: value,
          trailingComma: keepGoing,
          arena: self.arena
        )
      )
    } while keepGoing != nil

    return RawDocumentationAttributeArgumentListSyntax(elements: arguments, arena: self.arena)
  }
}

// MARK: Lookahead

extension Parser.Lookahead {
  mutating func atCustomAttributeArgument() -> Bool {
    var lookahead = self.lookahead()
    lookahead.skipSingle()

    // If we have any keyword, identifier, or token that follows a function
    // type's parameter list, this is a parameter list and not an attribute.
    // Alternatively, we might have a token that illustrates we're not going to
    // get anything following the attribute, which means the parentheses describe
    // what follows the attribute.
    switch lookahead.currentToken {
    case TokenSpec(.arrow),
      TokenSpec(.throwKeyword),
      TokenSpec(.throwsKeyword),
      TokenSpec(.rethrowsKeyword),
      TokenSpec(.rightParen),
      TokenSpec(.rightBrace),
      TokenSpec(.rightSquare),
      TokenSpec(.rightAngle):
      return false
    case _ where lookahead.at(.asyncKeyword):
      return false
    case _ where lookahead.at(.reasyncKeyword):
      return false
    default:
      return true
    }
  }

  mutating func canParseCustomAttribute() -> Bool {
    guard self.canParseType() else {
      return false
    }

    if self.at(TokenSpec(.leftParen, allowAtStartOfLine: false)) && self.withLookahead({ $0.atCustomAttributeArgument() }) {
      self.skipSingle()
    }

    return true
  }
}
