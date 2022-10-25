@_spi(RawSyntax) import SwiftSyntax
@_spi(RawSyntax) import SwiftParser

// Placeholder text must start with '<#' and end with
// '#>'.
//
// Placeholder kinds:
//
// Typed:
//   'T##' display-string '##' type-string ('##' type-for-expansion-string)?
//   'T##' display-and-type-string
//
// Basic:
//   display-string
//
// NOTE: It is required that '##' is not a valid substring of display-string
// or type-string. If this ends up not the case for some reason, we can consider
// adding escaping for '##'.

struct EditorPlaceholderData {
  enum Kind { case basic, typed }

  var kind: Kind
  var displayText: Substring
  var typeText: Substring
  var expansionTypeText: Substring

  init(token: TokenSyntax) {
    guard case .identifier(let tokenText) = token.tokenKind else {
      preconditionFailure("")
    }
    precondition(tokenText.hasPrefix("<#") &&
                 tokenText.hasSuffix("#>"))
    var text = tokenText.dropFirst(2).dropLast(2)

    // Basic.
    if !text.hasPrefix("T##") {
      kind = .basic
      displayText = text
      typeText = "_"
      expansionTypeText = self.typeText
      return
    }

    // Typed.
    self.kind = .typed

    // Drop 'T##'.
    text = text.dropFirst(3)

    // Parse the display text.
    (self.displayText, text) = splitEditorPlaceholderInterior(text)
    if text.isEmpty {
      self.typeText = self.displayText
      self.expansionTypeText = self.displayText
      return
    }

    // Parse the type text.
    (self.typeText, text) = splitEditorPlaceholderInterior(text)
    if text.isEmpty {
      self.expansionTypeText = self.typeText
      return
    }

    // The rest should be the expansion type text.
    self.expansionTypeText = text
  }
}

/// Split a string into two components separated by the first "##" in the
/// string. If '##' is not found, the second component will be empty.
private func splitEditorPlaceholderInterior(_ text: Substring) -> (Substring, Substring) {
  var idx = text.startIndex
  while idx != text.endIndex, !text[idx...].hasPrefix("##") {
    text.formIndex(after: &idx)
  }

  return (text[..<idx], text[text.index(idx, offsetBy: 2)...])
}

func expandPlaceholder<Node: SyntaxProtocol>(node: Node, offset: AbsolutePosition) -> Node {
  let syntax = Syntax(node)
  syntax.position
}


func text(token: TokenSyntax) {
  let data = EditorPlaceholderData(token: token)
  let expansionType: TypeSyntax = "\(data.expansionTypeText)"
}
