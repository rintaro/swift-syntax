@_spi(RawSyntax) import SwiftSyntax

/// Specialized parsing logic for macro expanded source code.
extension Parser {

  /// For 'member', 'peer' in type context.
  @_spi(MacroExpansion)
  public static func parseExpandedMemberDeclList(source: String) -> MemberDeclListSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var items: [RawMemberDeclListItemSyntax] = []
      var loopProgress = LoopProgressCondition()
      while !parser.at(.endOfFile) && loopProgress.evaluate(parser.currentToken) {
        guard let item = parser.parseMemberDeclListItem() else {
          break
        }
        items.append(item)
      }
      if !parser.at(.endOfFile) {
        if items.isEmpty {
          let missing = RawMissingDeclSyntax(attributes: nil, modifiers: nil, arena: parser.arena)
          items.append(RawMemberDeclListItemSyntax(decl: RawDeclSyntax(missing), semicolon: nil, arena: parser.arena))
        }

        // Parse remainder.
        items.append(parser.parseRemainder(into: items.removeLast()))
      }
      let raw = RawMemberDeclListSyntax(elements: items, arena: parser.arena)
      return Syntax(raw: RawSyntax(raw), rawNodeArena: parser.arena).cast(MemberDeclListSyntax.self)
    }
  }

  /// For 'accessor' macros (when the storage already has some accessors).
  @_spi(MacroExpansion)
  public static func parseExpandedAccessorList(source: String) -> AccessorListSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var items: [RawAccessorDeclSyntax] = []
      var loopProgress = LoopProgressCondition()
      while !parser.at(.endOfFile) && loopProgress.evaluate(parser.currentToken) {
        guard let introducer = parser.parseAccessorIntroducer() else {
          break
        }
        items.append(parser.parseAccessorDecl(introducer: introducer))
      }
      if !parser.at(.endOfFile) {
        // FIXME: Parse reminder even if 'items' is empty. Should we introduce MissingAccessor?
        if !items.isEmpty {
          // Parse remainder.
          items.append(parser.parseRemainder(into: items.removeLast()))
        }
      }
      let raw = RawAccessorListSyntax(elements: items, arena: parser.arena)
      return Syntax(raw: RawSyntax(raw), rawNodeArena: parser.arena).cast(AccessorListSyntax.self)
    }
  }

  /// For 'accessor' macros (when the storage doesn't have accessor block).
  @_spi(MacroExpansion)
  public static func parseExpandedAccessorBlock(source: String) -> AccessorBlockSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var parsed = parser.parseGetSet()
      parsed = parser.parseRemainder(into: parsed)
      return Syntax(raw: parsed.raw, rawNodeArena: parser.arena).cast(AccessorBlockSyntax.self)
    }
  }

  /// For 'memberAttribute' macros.
  @_spi(MacroExpansion)
  public static func parseExpandedAttributeList(source: String) -> AttributeListSyntax? {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var parsed = parser.parseAttributeList()
      if !parser.at(.endOfFile) {
        if parsed == nil {
          let missing = RawAttributeSyntax(
            atSign: parser.missingToken(.atSign),
            attributeName: RawTypeSyntax(RawMissingTypeSyntax(arena: parser.arena)),
            leftParen: nil,
            argument: nil,
            rightParen: nil,
            arena: parser.arena
          )
          parsed = RawAttributeListSyntax(elements: [.attribute(missing)], arena: parser.arena)
        }

        // Parse remainder.
        var attributes = parsed!.elements
        attributes.append(parser.parseRemainder(into: attributes.removeLast()))
        let elements = attributes.map {
          RawAttributeListSyntax.Element($0)!
        }
        parsed = RawAttributeListSyntax(elements: elements, arena: parser.arena)
      }
      return parsed.map {
        return Syntax(raw: $0.raw, rawNodeArena: parser.arena).cast(AttributeListSyntax.self)
      }
    }
  }

  /// For 'peer' macros at code block item position, or 'extension' macros.
  @_spi(MacroExpansion)
  public static func parseExpandedCodeBlockItemList(source: String, isAtTopLevel: Bool) -> CodeBlockItemListSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var parsed = parser.parseCodeBlockItemList(isAtTopLevel: isAtTopLevel, until: { $0.at(.endOfFile) })

      if !parser.at(.endOfFile) {
        var items = parsed.elements
        if items.isEmpty {
          let missing = RawMissingExprSyntax(arena: parser.arena)
          items.append(RawCodeBlockItemSyntax(item: .expr(RawExprSyntax(missing)), semicolon: nil, arena: parser.arena))
        }

        items.append(parser.parseRemainder(into: items.removeLast()))
        parsed = RawCodeBlockItemListSyntax(elements: items, arena: parser.arena)
      }
      return Syntax(raw: parsed.raw, rawNodeArena: parser.arena).cast(CodeBlockItemListSyntax.self)
    }
  }

  /// For @freestanding macros at code block item position.
  @_spi(MacroExpansion)
  public static func parseExpandedCodeBlockItem(source: String, isAtTopLevel: Bool) -> CodeBlockItemSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var parsed = parser.parseCodeBlockItem(isAtTopLevel: isAtTopLevel, allowInitDecl: true) ?? {
        let missing = RawMissingExprSyntax(arena: parser.arena)
        return RawCodeBlockItemSyntax(item: .expr(RawExprSyntax(missing)), semicolon: nil, arena: parser.arena)
      }()
      parsed = parser.parseRemainder(into: parsed)
      return Syntax(raw: parsed.raw, rawNodeArena: parser.arena).cast(CodeBlockItemSyntax.self)
    }
  }

  /// For @freestanding macros at member decl position.
  @_spi(MacroExpansion)
  public static func parseExpandedDeclMember(source: String) -> MemberDeclListItemSyntax {
    var parser = Parser(source)
    return withExtendedLifetime(parser) {
      var parsed = parser.parseMemberDeclListItem() ?? {
        let missing = RawMissingDeclSyntax(attributes: nil, modifiers: nil, arena: parser.arena)
        return RawMemberDeclListItemSyntax(decl: RawDeclSyntax(missing), semicolon: nil, arena: parser.arena)
      }()
      parsed = parser.parseRemainder(into: parsed)
      return Syntax(raw: parsed.raw, rawNodeArena: parser.arena).cast(MemberDeclListItemSyntax.self)
    }
  }

}
