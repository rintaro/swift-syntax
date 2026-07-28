//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2026 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

import Foundation
@_spi(_QualifiedLookup) @_spi(Experimental) import SwiftLexicalLookup
import SwiftParser
import SwiftSyntax
import XCTest

// TODO: Document `assertDirectLookup`; adapt all previous tests.
final class TestDirectLookup: XCTestCase {
  func testCodeBlockSimpleCase() {
    assertDirectLookup(
      """
      \(members: [
        // var a
        TestLookup(.identifier(identifier: "a")): ["1️⃣"],
        TestLookup(.identifier(identifier: "a", arguments: ["randomArg"])): ["1️⃣"],

        // var b
        TestLookup(.identifier(identifier: "b")): ["2️⃣"],

        // func hello
        TestLookup(.identifier(identifier: "hello", arguments: [])): ["3️⃣"],
        TestLookup(.identifier(identifier: "hello")): ["3️⃣"],

        // init
        TestLookup(.`init`(arguments: []), kind: .includeStatic): ["4️⃣"],
        TestLookup(.`init`(arguments: nil), kind: .includeStatic): ["4️⃣"],
        TestLookup(.unnamedCall(arguments: []), kind: .includeStatic): ["4️⃣"],

        // call as function
        TestLookup(.identifier(identifier: "callAsFunction", arguments: [])): ["5️⃣"],
        TestLookup(.identifier(identifier: "callAsFunction")): ["5️⃣"],
        TestLookup(.unnamedCall(arguments: [])): ["5️⃣"],

        // Enum cases
        TestLookup(.identifier(identifier: "case1"), kind: .includeStatic): ["6️⃣"],
        TestLookup(.identifier(identifier: "case1")): [], // instance-level yields no results
        TestLookup(.identifier(identifier: "case2", arguments: ["a"]), kind: .includeStatic): ["7️⃣"],

        // Static call as function
        TestLookup(.identifier(identifier: "callAsFunction", arguments: []), kind: .includeStatic): ["8️⃣"],

        // deinit
        TestLookup(.deinit): ["9️⃣"]
      ])
      struct MyStruct {
        // Test variables with no args plus args (MyStruct could be callable)
        var \("1️⃣")a,
            \("2️⃣")b: Int

        \("3️⃣") func hello() {}

        // Init can be referenced as <Type>.init, <Type>.init(), <Type>()
        \("4️⃣")
        init() {}

        // References: <myValue>.callAsFunction, <myValue>.callAsFunction(), <myValue>()
        \("5️⃣")
        func callAsFunction() {}

        // We assume the user meant static functions (diagnosed elsewhere)
        case \("6️⃣")case1,
             \("7️⃣")case2(a: Int)

        // When `callAsFunction` is static, it exhibits no special behavior
        static \("8️⃣")func callAsFunction () {}

        \("9️⃣")
        deinit {}
      }
      """
    )
  }
}
