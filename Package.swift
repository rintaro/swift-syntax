// swift-tools-version:5.3

import PackageDescription
import Foundation

/// If we are in a controlled CI environment, we can use internal compiler flags
/// to speed up the build or improve it.
let swiftSyntaxSwiftSettings: [SwiftSetting]
if ProcessInfo.processInfo.environment["SWIFT_BUILD_SCRIPT_ENVIRONMENT"] != nil {
  let groupFile = URL(fileURLWithPath: #file)
    .deletingLastPathComponent()
    .appendingPathComponent("utils")
    .appendingPathComponent("group.json")
  swiftSyntaxSwiftSettings = [.unsafeFlags([
    "-Xfrontend", "-group-info-path", 
    "-Xfrontend", groupFile.path, 
    // Enforcing exclusivity increases compile time of release builds by 2 minutes.
    // Disable it when we're in a controlled CI environment.
    "-enforce-exclusivity=unchecked",
  ])]
} else {
  swiftSyntaxSwiftSettings = []
}

/// If the `lib_InternalSwiftSyntaxParser.dylib` is not in the standard search
/// paths (which is the standard case on macOS),
/// `SWIFT_SYNTAX_PARSER_LIB_SEARCH_PATH` can be used to add a rpath at which
/// the parser lib should be searched.
let swiftSyntaxParserLinkerSettings: [LinkerSetting]
if let parserLibSearchPath = ProcessInfo.processInfo.environment["SWIFT_SYNTAX_PARSER_LIB_SEARCH_PATH"] {
  swiftSyntaxParserLinkerSettings = [.unsafeFlags([
    "-Xlinker", "-rpath", "-Xlinker", parserLibSearchPath
  ])]
} else {
  swiftSyntaxParserLinkerSettings = []
}

let package = Package(
  name: "SwiftSyntax",
  products: [
    .library(name: "SwiftSyntax", type: .static, targets: ["SwiftSyntax"]),
    .library(name: "SwiftSyntaxParser", type: .static, targets: ["SwiftSyntaxParser"]),
    .library(name: "SwiftSyntaxBuilder", type: .static, targets: ["SwiftSyntaxBuilder"]),
    .executable(name: "SwiftSyntaxBuilderGeneration", targets: ["SwiftSyntaxBuilderGeneration"])
  ],
  targets: [
    .target(
      name: "_CSwiftSyntax",
      exclude: [
        "README.md"
      ]
    ),
    .target(
      name: "SwiftSyntax",
      dependencies: ["_CSwiftSyntax"],
      exclude: [
        "RawSyntaxNodes.swift.gyb",
        "SyntaxFactory.swift.gyb",
        "SyntaxTraits.swift.gyb",
        "TriviaPiece.swift.gyb",
        "Misc.swift.gyb",
        "SyntaxRewriter.swift.gyb",
        "SyntaxEnum.swift.gyb",
        "SyntaxClassification.swift.gyb",
        "SyntaxBuilders.swift.gyb",
        "TokenKind.swift.gyb",
        "SyntaxValidation.swift.gyb",
        "SyntaxVisitor.swift.gyb",
        "SyntaxCollections.swift.gyb",
        "SyntaxBaseNodes.swift.gyb",
        "SyntaxAnyVisitor.swift.gyb",
        "SyntaxNodes.swift.gyb.template",
        "SyntaxKind.swift.gyb",
      ],
      swiftSettings: swiftSyntaxSwiftSettings
    ),
    .target(
      name: "SwiftSyntaxBuilder",
      dependencies: ["SwiftSyntax"],
      exclude: [
        "gyb_helpers",
        "BuildableCollectionNodes.swift.gyb",
        "BuildableNodes.swift.gyb",
        "ResultBuilders.swift.gyb",
      ]
    ),
    .target(
      name: "SwiftSyntaxParser",
      dependencies: ["SwiftSyntax"],
      exclude: [
        "NodeDeclarationHash.swift.gyb"
      ],
      linkerSettings: swiftSyntaxParserLinkerSettings
    ),
    .target(
      name: "lit-test-helper",
      dependencies: ["SwiftSyntax", "SwiftSyntaxParser"]
    ),
    .target(
        name: "SwiftSyntaxBuilderGeneration",
        dependencies: ["SwiftSyntaxBuilder"],
        exclude: [
          "gyb_helpers",
          "AttributeNodes.swift.gyb",
          "AvailabilityNodes.swift.gyb",
          "BuilderInitializableTypes.swift.gyb",
          "Classification.swift.gyb",
          "CommonNodes.swift.gyb",
          "DeclNodes.swift.gyb",
          "ExpressibleAsConformances.swift.gyb",
          "ExprNodes.swift.gyb",
          "GenericNodes.swift.gyb",
          "Kinds.swift.gyb",
          "NodeSerializationCodes.swift.gyb",
          "PatternNodes.swift.gyb",
          "StmtNodes.swift.gyb",
          "SyntaxBaseKinds.swift.gyb",
          "Tokens.swift.gyb",
          "Traits.swift.gyb",
          "Trivia.swift.gyb",
          "TypeNodes.swift.gyb"
        ]
    ),
    .testTarget(
      name: "SwiftSyntaxTest",
      dependencies: ["SwiftSyntax"]
    ),
    .testTarget(
      name: "SwiftSyntaxBuilderTest",
      dependencies: ["SwiftSyntaxBuilder"]
    ),
    .testTarget(
      name: "SwiftSyntaxParserTest",
      dependencies: ["SwiftSyntaxParser"],
      exclude: ["Inputs"]
    ),
    .testTarget(
      name: "PerformanceTest",
      dependencies: ["SwiftSyntax", "SwiftSyntaxParser"],
      exclude: ["Inputs"]
    ),
  ]
)
