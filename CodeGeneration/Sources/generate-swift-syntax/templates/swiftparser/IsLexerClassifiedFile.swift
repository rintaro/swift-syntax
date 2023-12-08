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

import SwiftSyntax
import SwiftSyntaxBuilder
import SyntaxSupport
import Utils

let isLexerClassifiedFile = SourceFileSyntax(leadingTrivia: copyrightHeader) {
  DeclSyntax("@_spi(RawSyntax) import SwiftSyntax")

  try! ExtensionDeclSyntax(
    """
    extension RawTokenKind
    """
  ) {
    try! FunctionDeclSyntax(
      """
      static func lexerClassifiedKeyword(from text: SyntaxText) -> Self?
      """
    ) {
      try! SwitchExprSyntax("switch text.count") {
        for (length, keywords) in keywordsByLength() {
          let keywords = keywords.filter({ $0.isLexerClassified })
          if keywords.count > 0 {
            SwitchCaseSyntax("case \(raw: length):") {
              try! SwitchExprSyntax("switch text") {
                for keyword in keywords {
                  SwitchCaseSyntax("case \(literal: keyword.name):") {
                    ExprSyntax("return .\(keyword.rawTokenKindCaseName)")
                  }
                }
                SwitchCaseSyntax("default: return nil")
              }
            }
          }
        }
        SwitchCaseSyntax("default: return nil")
      }
    }

    try! VariableDeclSyntax(
      """
      /// Whether the token kind is switched from being an identifier to being a keyword in the lexer.
      /// This is true for keywords that used to be considered non-contextual.
      var isLexerClassifiedKeyword: Bool
      """
    ) {
      try! SwitchExprSyntax("switch self") {
        for keywordSpec in Keyword.allCases.map(\.spec) {
          if keywordSpec.isLexerClassified {
            SwitchCaseSyntax("case .\(keywordSpec.rawTokenKindCaseName): return true")
          }
        }
        SwitchCaseSyntax("default: return false")
      }
    }
  }

  try! ExtensionDeclSyntax(
    """
    extension Keyword
    """
  ) {
    try! VariableDeclSyntax(
      """
      /// Whether the token kind is switched from being an identifier to being a keyword in the lexer.
      /// This is true for keywords that used to be considered non-contextual.
      var isLexerClassified: Bool
      """
    ) {
      try! SwitchExprSyntax("switch self") {
        for keyword in Keyword.allCases {
          if keyword.spec.isLexerClassified {
            SwitchCaseSyntax("case .\(keyword.spec.varOrCaseName): return true")
          }
        }
        SwitchCaseSyntax("default: return false")
      }
    }
  }

  try! ExtensionDeclSyntax(
    """
    extension TokenKind
    """
  ) {
    try! VariableDeclSyntax(
      """
      /// Returns `true` if the token is a Swift keyword.
      ///
      /// Keywords are reserved unconditionally for use by Swift and may not
      /// appear as identifiers in any position without being escaped. For example,
      /// `class`, `func`, or `import`.
      @_spi(Diagnostics) @_spi(Testing)
      public var isLexerClassifiedKeyword: Bool
      """
    ) {
      try! SwitchExprSyntax("switch self") {
        SwitchCaseSyntax("case .keyword(let keyword):") {
          StmtSyntax("return keyword.isLexerClassified")
        }
        SwitchCaseSyntax("default: return false")
      }
    }
  }
}
