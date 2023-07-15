//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2023 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

import SwiftSyntax

extension SyntaxProtocol {
  var baseIndentation: String {

    // Look for syntactically independent item (i.e. statement) this node belongs.
    var node = Syntax(self)
    while !node.is(CodeBlockItemSyntax.self) &&
        !node.is(MemberDeclListItemSyntax.self) &&
        !node.is(AccessorDeclSyntax.self) &&
        !node.is(SwitchCaseSyntax.self) {
      guard let parent = node.parent else {
        break
      }
      node = parent
    }

    // Infer the indentation of that node.
    var indentation = ""
    var hadCommentOnThisLine = false
    for piece in node.leadingTrivia {
      switch piece {
      case .tabs, .spaces:
        // ```
        //     /* private */ func foo() {}
        //     ↑ here the indentation
        //                   ↑ not here
        // ```
        if !hadCommentOnThisLine {
          piece.write(to: &indentation)
        }

      case .carriageReturns, .carriageReturnLineFeeds, .formfeeds, .newlines, .verticalTabs:
        // Reset the indentation on 'isNewline' pieces.
        indentation = ""
        hadCommentOnThisLine = false

      case .blockComment, .docBlockComment:
        hadCommentOnThisLine = true

      case .docLineComment, .lineComment, .shebang:
        // Ignore line comment pieces.
        break

      case .backslashes, .pounds, .unexpectedText:
        // Ignore line comment pieces.
        break
      }
    }
    return indentation
  }
}

extension String {
  func applying(indentation: String) -> String {
    if isEmpty || indentation.isEmpty {
      return self
    }

    var indented = ""
    var remaining = self[...]
    while let nextNewline = remaining.firstIndex(where: { $0.isNewline }) {
      if nextNewline != remaining.startIndex {
        indented += indentation
      }
      indented += remaining[...nextNewline]
      remaining = remaining[remaining.index(after: nextNewline)...]
    }

    if !remaining.isEmpty {
      indented += indentation
      indented += remaining
    }

    return indented
  }
}

/// Adjust expanded code to suit
func adjustMacroExpansionWhitespace(macroRole: MacroRole, expandedCode: String) -> String {

  switch macroRole {
  case .expression, .declaration, .codeItem:
    // Freestanding macros inherits the trivia of the expansion syntax.
    // So no adjustment is needed.
    return expandedCode
  case .member, .peer, .conformance, .extension:
    // Expanded declaration list is inserted after the last element of the
    // block, which ends right before the newline (i.e. trailing trivia doesn't contain newlines).
    return "\n\n" + expandedCode
  case .memberAttribute:
    // Attributes are inserted either
    //  * right after the last attribute
    //  * if there's no attributes, after the leading trivia of the target
    return "\n" + expandedCode
  case .accessor:
    /// var value: Int
    return "\n" + expandedCode
  }
}
