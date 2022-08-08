import XCTest
import SwiftSyntax
import SwiftSyntaxParser

public class ParsingPerformanceTests: XCTestCase {

  var inputFile: URL {
    return URL(fileURLWithPath: #file)
      .deletingLastPathComponent()
      .appendingPathComponent("Inputs")
      .appendingPathComponent("MinimalCollections.swift.input")
  }

  func testParsingPerformance() {
    measure {
      do {
        for _ in 0 ..< 500 {
        _ = try SyntaxParser.parse(inputFile)
        }
      } catch {
        XCTFail(error.localizedDescription)
      }
    }
  }
}
