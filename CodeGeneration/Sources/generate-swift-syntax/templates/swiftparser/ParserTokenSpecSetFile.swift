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

/// A `switch` case that assigns `self` when the scrutinee is `enumCaseCallName`.
///
/// When further cases follow in a later `switch`, the assignment is followed by a
/// `return` so that those cases are not also considered.
func matchCase(
  _ enumCaseCallName: TokenSyntax,
  experimentalFeature: ExperimentalFeature?,
  isLast: Bool
) -> SwitchCaseSyntax {
  var whereClause = ""
  if let feature = experimentalFeature {
    whereClause += " where languageFeatures.contains(.\(feature.token))"
  }
  let body = isLast ? "self = .\(enumCaseCallName)" : "self = .\(enumCaseCallName)\nreturn"
  return "case .\(enumCaseCallName)\(raw: whereClause): \(raw: body)"
}

let parserTokenSpecSetFile = SourceFileSyntax(leadingTrivia: copyrightHeader) {
  importSwiftSyntax(accessLevel: .public)

  for layoutNode in SYNTAX_NODES.compactMap(\.layoutNode) {
    for child in layoutNode.children {
      if case let .token(choices, _, _) = child.kind, choices.count > 1 {
        try! ExtensionDeclSyntax("extension \(layoutNode.kind.syntaxType)") {
          try EnumDeclSyntax(
            """
            @_spi(Diagnostics)
            public enum \(child.tokenSpecSetType): TokenSpecSet
            """
          ) {
            for choice in choices {
              switch choice {
              case .keyword(let keyword):
                DeclSyntax(
                  """
                  \(keyword.spec.apiAttributes)\
                  case \(keyword.spec.enumCaseDeclName)
                  """
                )
              case .token(let token):
                DeclSyntax("case \(token.spec.enumCaseDeclName)")
              }
            }

            // A token choice is matched on the lexeme's kind, a keyword choice on the
            // keyword that the lexer resolved for it. Switching instead of comparing
            // against one `TokenSpec` per choice lets the compiler build a jump table.
            //
            // The token choices are checked first: an `identifier` choice takes
            // precedence over a keyword choice, and every set that has both spells
            // `identifier` ahead of its keywords.
            let tokenChoices: [(TokenSyntax, ExperimentalFeature?)] = choices.compactMap {
              if case .token(let token) = $0 {
                return (token.spec.enumCaseCallName, token.spec.experimentalFeature)
              }
              return nil
            }
            let keywordChoices: [(TokenSyntax, ExperimentalFeature?)] = choices.compactMap {
              if case .keyword(let keyword) = $0 {
                return (keyword.spec.enumCaseCallName, keyword.spec.experimentalFeature)
              }
              return nil
            }

            try InitializerDeclSyntax(
              "init?(lexeme: Lexer.Lexeme, languageFeatures: Parser.LanguageFeatures)"
            ) {
              if !tokenChoices.isEmpty {
                try SwitchExprSyntax("switch lexeme.rawTokenKind") {
                  for (caseName, feature) in tokenChoices {
                    matchCase(caseName, experimentalFeature: feature, isLast: keywordChoices.isEmpty)
                  }
                  if keywordChoices.isEmpty {
                    SwitchCaseSyntax("default: return nil")
                  } else {
                    SwitchCaseSyntax("default: break")
                  }
                }
              }
              if !keywordChoices.isEmpty {
                // Bind the keyword before switching on it: in a `switch` over
                // `Keyword?`, `case .none` and `case .some` would name the optional's
                // cases rather than the keywords spelled `none` and `some`.
                StmtSyntax("guard let keyword = lexeme.keyword else { return nil }")
                try SwitchExprSyntax("switch keyword") {
                  for (caseName, feature) in keywordChoices {
                    matchCase(caseName, experimentalFeature: feature, isLast: true)
                  }
                  SwitchCaseSyntax("default: return nil")
                }
              }
            }

            try InitializerDeclSyntax("public init?(token: TokenSyntax)") {
              try SwitchExprSyntax("switch token") {
                for choice in choices {
                  SwitchCaseSyntax(
                    "case TokenSpec(.\(choice.enumCaseCallName)): self = .\(choice.enumCaseCallName)"
                  )
                }
                SwitchCaseSyntax("default: return nil")
              }
            }

            try VariableDeclSyntax("var spec: TokenSpec") {
              try SwitchExprSyntax("switch self") {
                for choice in choices {
                  switch choice {
                  case .keyword(let keyword):
                    let caseName = keyword.spec.enumCaseCallName
                    SwitchCaseSyntax("case .\(caseName): return .keyword(.\(caseName))")
                  case .token(let token):
                    let caseName = token.spec.enumCaseCallName
                    SwitchCaseSyntax("case .\(caseName): return .\(caseName)")
                  }
                }
              }
            }

            try VariableDeclSyntax(
              """
              /// Returns a token that satisfies the `TokenSpec` of this case.
              ///
              /// If the token kind of this spec has variable text, e.g. for an identifier, this returns a token with empty text.
              @_spi(Diagnostics)
              public var tokenSyntax: TokenSyntax
              """
            ) {
              try SwitchExprSyntax("switch self") {
                for choice in choices {
                  switch choice {
                  case .keyword(let keyword):
                    let caseName = keyword.spec.enumCaseCallName
                    SwitchCaseSyntax("case .\(caseName): return .keyword(.\(caseName))")
                  case .token(let token):
                    let caseName = token.spec.enumCaseCallName
                    if token.spec.text != nil {
                      SwitchCaseSyntax("case .\(caseName): return .\(caseName)Token()")
                    } else {
                      SwitchCaseSyntax(#"case .\#(caseName): return .\#(caseName)("")"#)
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
