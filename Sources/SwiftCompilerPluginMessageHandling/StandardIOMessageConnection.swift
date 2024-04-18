//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift open source project
//
// Copyright (c) 2023-2024 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#if swift(>=6.0)
private import _CShims
#if canImport(Darwin)
private import Darwin
#elseif canImport(Glibc)
private import Glibc
#elseif canImport(ucrt)
private import ucrt
#endif
#else
import _CShims
#if canImport(Darwin)
import Darwin
#elseif canImport(Glibc)
import Glibc
#elseif canImport(ucrt)
import ucrt
#endif
#endif

#if canImport(ucrt)
private let dup = _dup(_:)
private let fileno = _fileno(_:)
private let dup2 = _dup2(_:_:)
private let close = _close(_:)
private let read = _read(_:_:_:)
private let write = _write(_:_:_:)
#endif

/// Message connection for executable plugins, uses standard I/O as the transport layer.
@_spi(PluginMessage)
public struct StandardIOMessageConnection: MessageConnection {
  private let inputFD: CInt
  private let outputFD: CInt

  public init() throws {
    let stdin = _ss_stdin()
    let stdout = _ss_stdout()
    let stderr = _ss_stderr()

    // Duplicate the `stdin` file descriptor, which we will then use for
    // receiving messages from the plugin host.
    inputFD = dup(fileno(stdin))
    guard inputFD >= 0 else {
      throw IOError.systemError(funcName: "dup(2)", errno: _ss_errno())
    }

    // Having duplicated the original standard-input descriptor, we close
    // `stdin` so that attempts by the plugin to read console input (which
    // are usually a mistake) return errors instead of blocking.
    guard close(fileno(stdin)) >= 0 else {
      throw IOError.systemError(funcName: "close(2)", errno: _ss_errno())
    }

    // Duplicate the `stdout` file descriptor, which we will then use for
    // sending messages to the plugin host.
    outputFD = dup(fileno(stdout))
    guard outputFD >= 0 else {
      throw IOError.systemError(funcName: "dup(2)", errno: _ss_errno())
    }

    // Having duplicated the original standard-output descriptor, redirect
    // `stdout` to `stderr` so that all free-form text output goes there.
    guard dup2(fileno(stderr), fileno(stdout)) >= 0 else {
      throw IOError.systemError(funcName: "dup2(2)", errno: _ss_errno())
    }

    #if canImport(ucrt)
    // Set I/O to binary mode. Avoid CRLF translation, and Ctrl+Z (0x1A) as EOF.
    _ = _setmode(inputFD, _O_BINARY)
    _ = _setmode(outputFD, _O_BINARY)
    #endif
  }

  /// Write the buffer to 'outputFD', throws an error on failure.
  private func _write(contentsOf buffer: UnsafeRawBufferPointer) throws {
    guard var ptr = buffer.baseAddress else { return }
    let endPtr = ptr.advanced(by: buffer.count)
    while ptr != endPtr {
      switch write(outputFD, ptr, numericCast(endPtr - ptr)) {
      case -1: throw IOError.systemError(funcName: "write(2)", errno: _ss_errno())
      case 0: throw IOError.systemError(funcName: "write(2)", errno: 0) /* unreachable */
      case let n: ptr += Int(n)
      }
    }
  }

  /// Fill the buffer from 'inputFD'. Throws an error on failure.
  /// If the file descriptor reached the end-of-file, throws IOError.readReachedEndOfInput
  private func _read(into buffer: UnsafeMutableRawBufferPointer) throws {
    guard var ptr = buffer.baseAddress else { return }
    let endPtr = ptr.advanced(by: buffer.count)
    while ptr != endPtr {
      switch read(inputFD, ptr, numericCast(endPtr - ptr)) {
      case -1: throw IOError.systemError(funcName: "read(2)", errno: _ss_errno())
      case 0: throw IOError.readReachedEndOfInput
      case let n: ptr += Int(n)
      }
    }
  }

  // MARK: - MessageConnection conformance

  public func sendMessage<TX: Encodable>(_ message: TX) throws {
    // Encode the message as JSON.
    let payload = try JSON.encode(message)

    // Write the header (a 64-bit length field in little endian byte order).
    let count = payload.count
    var header = UInt64(count).littleEndian
    try withUnsafeBytes(of: &header) { try _write(contentsOf: $0) }

    // Write the JSON payload.
    try payload.withUnsafeBytes { try _write(contentsOf: $0) }
  }

  public func waitForNextMessage<RX: Decodable>(_ ty: RX.Type) throws -> RX? {
    // Read the header (a 64-bit length field in little endian byte order).
    var header: UInt64 = 0
    do {
      try withUnsafeMutableBytes(of: &header) { try _read(into: $0) }
    } catch IOError.readReachedEndOfInput {
      // Connection closed.
      return nil
    }

    // Read the JSON payload.
    let count = Int(UInt64(littleEndian: header))
    let data = UnsafeMutableRawBufferPointer.allocate(byteCount: count, alignment: 1)
    defer { data.deallocate() }
    try _read(into: data)

    // Decode and return the message.
    return try JSON.decode(ty, from: UnsafeBufferPointer(data.bindMemory(to: UInt8.self)))
  }
}

private enum IOError: Error, CustomStringConvertible {
  case readReachedEndOfInput
  case systemError(funcName: String, errno: CInt)

  var description: String {
    switch self {
    case .readReachedEndOfInput: "reached end-of-file"
    case .systemError(let funcName, let errno): "\(funcName) failed: \(describe(errno: errno))"
    }
  }
}

// Private function to construct an error message from an `errno` code.
private func describe(errno: CInt) -> String {
  if let cStr = strerror(errno) { return String(cString: cStr) }
  return String(describing: errno)
}
