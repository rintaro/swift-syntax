
@_spi(RawSyntax) internal import SwiftSyntax
// MARK: - Raw

extension RawMissingDeclSyntax {
  init(
    attributes: RawAttributeListSyntax,
    modifiers: RawDeclModifierListSyntax,
    arena: __shared RawSyntaxArena
  ) {
    self.init(
      attributes: attributes,
      modifiers: modifiers,
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#declaration#>", arena: arena),
      arena: arena
    )
  }
}

extension RawMissingExprSyntax {
  init(arena: __shared RawSyntaxArena) {
    self.init(
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#expression#>", arena: arena),
      arena: arena
    )
  }
}

extension RawMissingPatternSyntax {
  init(arena: __shared RawSyntaxArena) {
    self.init(
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#pattern#>", arena: arena),
      arena: arena
    )
  }
}

extension RawMissingStmtSyntax {
  init(arena: __shared RawSyntaxArena) {
    self.init(
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#statement#>", arena: arena),
      arena: arena
    )
  }
}

extension RawMissingTypeSyntax {
  init(arena: __shared RawSyntaxArena) {
    self.init(
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#type#>", arena: arena),
      arena: arena
    )
  }
}

extension RawMissingSyntax {
  init(arena: __shared RawSyntaxArena) {
    self.init(
      placeholder: RawTokenSyntax(missing: .identifier, text: "<#syntax#>", arena: arena),
      arena: arena
    )
  }
}
