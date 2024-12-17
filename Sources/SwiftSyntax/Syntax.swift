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

#if compiler(>=6)
@_implementationOnly private import _SwiftSyntaxCShims
#else
@_implementationOnly import _SwiftSyntaxCShims
#endif

// `Syntax` is a user facing "red" tree. A value is a pair of strong reference to
// the _arena_ and a pointer to the `SyntaxData` allocated in the arena.
// The _arena_ is shared between the all node in the tree and only in the tree.
// Whenever the tree is modified, a new arena is created and it forms a new "tree".

/// A Syntax node represents a tree of nodes with tokens at the leaves.
/// Each node has accessors for its known children, and allows efficient
/// iteration over the children through its `children` property.
public struct Syntax: SyntaxProtocol, SyntaxHashable {
  let arena: SyntaxDataArena
  let dataRef: SyntaxDataReference

  /// "designated" memberwise initializer of `Syntax`.
  @_transparent  // Inline early to enable certain optimzation.
  init(arena: __shared SyntaxDataArena, dataRef: SyntaxDataReference) {
    self.arena = arena
    self.dataRef = dataRef
  }

  @inline(__always)
  private var data: SyntaxData {
    @_transparent unsafeAddress { dataRef.pointer }
  }

  @inline(__always)
  var raw: RawSyntax {
    data.raw
  }

  @inline(__always)
  public var root: Self {
    return Self(arena: arena, dataRef: arena.root)
  }

  @inline(__always)
  public var parent: Self? {
    data.parent.map { Self(arena: arena, dataRef: $0) }
  }

  @inline(__always)
  public var hasParent: Bool {
    data.parent != nil
  }

  var absoluteInfo: AbsoluteSyntaxInfo {
    data.absoluteInfo
  }

  /// Index in parent's layout. `nil` slots are counted.
  var layoutIndexInParent: Int {
    Int(absoluteInfo.layoutIndexInParent)
  }

  public var id: SyntaxIdentifier {
    SyntaxIdentifier(
      rootId: UInt(rawID: arena.root.pointee.raw.id),
      indexInTree: SyntaxIdentifier.SyntaxIndexInTree(indexInTree: absoluteInfo.indexInTree)
    )
  }

  /// The position of the start of this node's leading trivia
  public var position: AbsolutePosition {
    AbsolutePosition(utf8Offset: Int(absoluteInfo.offset))
  }

  /// The position of the start of this node's content, skipping its trivia
  public var positionAfterSkippingLeadingTrivia: AbsolutePosition {
    return position + raw.leadingTriviaLength
  }

  /// The end position of this node's content, before any trailing trivia.
  public var endPositionBeforeTrailingTrivia: AbsolutePosition {
    return endPosition - raw.trailingTriviaLength
  }

  /// The end position of this node, including its trivia.
  public var endPosition: AbsolutePosition {
    position + raw.totalLength
  }

  /// Creates a ``Syntax`` for a root raw node.
  ///
  /// - Parameters:
  ///   - raw: The raw node that will be the root of the tree
  ///   - rawNodeArena: The arena in which `raw` is allocated. It is passed to
  ///     make sure the arena doesn’t get de-allocated before the ``Syntax``
  ///     has a chance to retain it.
  static func forRoot(_ raw: RawSyntax, rawNodeArena: RetainedSyntaxArena) -> Syntax {
    precondition(rawNodeArena == raw.arenaReference)
    let arena = SyntaxDataArena(raw: raw, rawNodeArena: rawNodeArena)
    return Self(arena: arena, dataRef: arena.root)
  }

  static func forRoot(_ raw: RawSyntax, rawNodeArena: SyntaxArena) -> Syntax {
    return forRoot(raw, rawNodeArena: RetainedSyntaxArena(rawNodeArena))
  }

  /// References to the children data.
  ///
  /// - Note: The buffer is managed by the arena, and thus only valid while the arena is alive.
  var layoutBuffer: SyntaxDataReferenceBuffer {
    self.arena.layout(for: self.dataRef)
  }

  /// Returns the child node at the provided index in this node's layout.
  /// - Note: This function traps if the node is a token, or the index is out of the bounds of the layout.
  ///
  /// - Parameter index: The index to create and cache.
  /// - Returns: The child's node at the provided index.
  func child(at index: Int) -> Syntax? {
    let layoutBuffer = self.layoutBuffer
    guard let dataRef = layoutBuffer[index] else {
      return nil
    }
    return Self(arena: self.arena, dataRef: dataRef)
  }

  /// Creates a copy of `self` and recursively creates ``Syntax`` nodes up to
  /// the root.
  ///
  /// - Parameters:
  ///   - newRaw: The node that should replace `self`
  ///   - rawNodeArena: The arena in which `newRaw` resides
  ///   - allocationArena: The arena in which  new nodes should be allocated
  /// - Returns: A syntax tree with all parents where this node has been
  ///            replaced by `newRaw`
  func replacingSelf(_ newRaw: RawSyntax, rawNodeArena: RetainedSyntaxArena, allocationArena: SyntaxArena) -> Syntax {
    precondition(newRaw.arenaReference == rawNodeArena)
    // If we have a parent already, then ask our current parent to copy itself
    // recursively up to the root.
    if let parent {
      let newParent = parent.replacingChild(
        at: layoutIndexInParent,
        with: newRaw,
        rawNodeArena: rawNodeArena,
        allocationArena: allocationArena
      )
      return newParent.child(at: layoutIndexInParent)!
    } else {
      // Otherwise, we're already the root, so return the new root data.
      return .forRoot(newRaw, rawNodeArena: rawNodeArena)
    }
  }

  /// Creates a copy of `self` with the child at the provided index replaced
  /// with a new ``Syntax`` containing the raw syntax provided.
  ///
  /// - Parameters:
  ///   - index: The index pointing to where in the raw layout to place this
  ///            child.
  ///   - newChild: The raw syntax for the new child to replace.
  ///   - newChildArena: The arena in which `newChild` resides.
  ///   - arena: The arena in which the new node will be allocated.
  /// - Returns: The new root node created by this operation, and the new child
  ///            syntax data.
  /// - SeeAlso: replacingSelf(_:)
  func replacingChild(
    at index: Int,
    with newChild: RawSyntax?,
    rawNodeArena: RetainedSyntaxArena?,
    allocationArena: SyntaxArena
  ) -> Syntax {
    precondition(newChild == nil || (rawNodeArena != nil && newChild!.arenaReference == rawNodeArena!))
    // After newRaw has been allocated in `allocationArena`, `rawNodeArena` will
    // be a child arena of `allocationArena` and thus, `allocationArena` will
    // keep `newChild` alive.
    let newRaw = withExtendedLifetime(rawNodeArena) {
      raw.layoutView!.replacingChild(at: index, with: newChild, arena: allocationArena)
    }
    return replacingSelf(newRaw, rawNodeArena: RetainedSyntaxArena(allocationArena), allocationArena: allocationArena)
  }

  /// Same as `replacingChild(at:with:rawNodeArena:allocationArena:)` but takes a `__SyntaxArena` instead of a `RetainedSyntaxArena`.
  func replacingChild(
    at index: Int,
    with newChild: RawSyntax?,
    rawNodeArena: SyntaxArena?,
    allocationArena: SyntaxArena
  ) -> Syntax {
    return self.replacingChild(
      at: index,
      with: newChild,
      rawNodeArena: rawNodeArena.map(RetainedSyntaxArena.init),
      allocationArena: allocationArena
    )
  }

  /// Identical to `replacingChild(at: Int, with: RawSyntax?, arena: SyntaxArena)`
  /// that ensures that the arena of`newChild` doesn’t get de-allocated before
  /// `newChild` has been addded to the result.
  func replacingChild(at index: Int, with newChild: Syntax?, arena: SyntaxArena) -> Syntax {
    return withExtendedLifetime(newChild) {
      return replacingChild(
        at: index,
        with: newChild?.raw,
        rawNodeArena: newChild?.raw.arenaReference.retained,
        allocationArena: arena
      )
    }
  }

  func withLeadingTrivia(_ leadingTrivia: Trivia, arena: SyntaxArena) -> Syntax {
    if let raw = raw.withLeadingTrivia(leadingTrivia, arena: arena) {
      return replacingSelf(raw, rawNodeArena: RetainedSyntaxArena(arena), allocationArena: arena)
    } else {
      return self
    }
  }

  func withTrailingTrivia(_ trailingTrivia: Trivia, arena: SyntaxArena) -> Syntax {
    if let raw = raw.withTrailingTrivia(trailingTrivia, arena: arena) {
      return replacingSelf(raw, rawNodeArena: RetainedSyntaxArena(arena), allocationArena: arena)
    } else {
      return self
    }
  }

  func withPresence(_ presence: SourcePresence, arena: SyntaxArena) -> Syntax {
    if let raw = raw.tokenView?.withPresence(presence, arena: arena) {
      return replacingSelf(raw, rawNodeArena: RetainedSyntaxArena(arena), allocationArena: arena)
    } else {
      return self
    }
  }

  func ancestorOrSelf<T>(mapping map: (Syntax) -> T?) -> T? {
    if let r = map(self) {
      return r
    }
    var dataRef = self.dataRef
    while let parent = dataRef.pointee.parent {
      dataRef = parent
      if let r = map(Syntax(arena: arena, dataRef: dataRef)) {
        return r
      }
    }
    return nil
  }

  /// Needed for the conformance to ``SyntaxProtocol``. Just returns `self`.
  public var _syntaxNode: Syntax {
    return self
  }

  @_spi(RawSyntax)
  public init(raw: RawSyntax, rawNodeArena: __shared RetainedSyntaxArena) {
    self = .forRoot(raw, rawNodeArena: rawNodeArena)
  }

  @_spi(RawSyntax)
  public init(raw: RawSyntax, rawNodeArena: __shared SyntaxArena) {
    self = .forRoot(raw, rawNodeArena: RetainedSyntaxArena(rawNodeArena))
  }

  /// Create a ``Syntax`` node from a specialized syntax node.
  // Inline always so the optimizer can optimize this to a member access on `syntax` without having to go through
  // generics.
  @_transparent
  public init(_ syntax: __shared some SyntaxProtocol) {
    self = syntax._syntaxNode
  }

  /// Creates a new ``Syntax`` node from any node that conforms to ``SyntaxProtocol``.
  public init(fromProtocol syntax: __shared SyntaxProtocol) {
    self = syntax._syntaxNode
  }

  /// Same as ``init(fromProtocol:)`` but returns `nil` if `syntax` is `nil`.
  public init?(fromProtocol syntax: __shared SyntaxProtocol?) {
    guard let syntax = syntax else { return nil }
    self = syntax._syntaxNode
  }

  /// Syntax nodes always conform to SyntaxProtocol. This API is just added
  /// for consistency.
  /// Note that this will incur an existential conversion.
  @available(*, deprecated, message: "Expression always evaluates to true")
  public func isProtocol(_: SyntaxProtocol.Protocol) -> Bool {
    return true
  }

  /// Return the non-type erased version of this syntax node.
  /// Note that this will incur an existential conversion.
  public func asProtocol(_: SyntaxProtocol.Protocol) -> SyntaxProtocol {
    return self.raw.kind.syntaxNodeType.init(self)!
  }

  /// Add the hash value of this node’s ID to `hasher`.
  public func hash(into hasher: inout Hasher) {
    return id.hash(into: &hasher)
  }

  /// Returns `true` if `rhs` and `lhs` have the same ID.
  ///
  /// Note `lhs` and `rhs` might have the same contents even if their IDs are
  /// different. See documentation on ``SyntaxIdentifier``.
  public static func == (lhs: Syntax, rhs: Syntax) -> Bool {
    return lhs.id == rhs.id
  }
}

extension Syntax: Identifiable {
  /// ``SyntaxIdentifier`` uniquely identifies a node.
  public typealias ID = SyntaxIdentifier
}

extension Syntax {
  /// Retrieve the syntax text as an array of bytes that models the input
  /// source even in the presence of invalid UTF-8.
  public var syntaxTextBytes: [UInt8] {
    return raw.syntaxTextBytes
  }
}

typealias SyntaxDataReference = SyntaxArenaAllocatedPointer<SyntaxData>
typealias SyntaxDataReferenceBuffer = SyntaxArenaAllocatedBufferPointer<SyntaxDataReference?>

/// Node data for a `Syntax`, allocated and managed by `SyntaxDataArena`.
/// NOTE: This type must be trivial as it is allocated by ‘BumpPtrAllocator’.
struct SyntaxData: Sendable {
  /// Underlying "green" node of this node
  let raw: RawSyntax
  /// Reference to the parent data. Or `nil` if this is the root.
  let parent: SyntaxDataReference?
  /// Index and position info in the tree.
  let absoluteInfo: AbsoluteSyntaxInfo
  /// Length of the children layout.
  /// This is a cached information, equals to `raw.layoutView?.children.count ?? 0`.
  let childCount: UInt32

  // If the childCount > 0, the layout buffer (`SyntaxDataArenaReference? * childCount`) is tail allocated.
}

/// `SyntaxDataArena` manages the entire data of a "red" tree.
final class SyntaxDataArena: @unchecked Sendable {
  /// Mutex for locking the data when populating layout buffers.
  private let mutex: PlatformMutex

  /// Allocator.
  private let allocator: BumpPtrAllocator

  /// Retaining reference to the arena of the _root_ ``RawSyntax``
  private let rawArena: RetainedSyntaxArena

  /// Root node.
  let root: SyntaxDataReference

  init(raw: RawSyntax, rawNodeArena: RetainedSyntaxArena) {
    precondition(rawNodeArena == raw.arenaReference)
    assert(MemoryLayout<SyntaxData>.alignment >= MemoryLayout<UnsafePointer<SyntaxData>?>.alignment)

    self.mutex = PlatformMutex.create()
    self.allocator = BumpPtrAllocator(initialSlabSize: Self.slabSize(for: raw))
    self.rawArena = rawNodeArena
    self.root = Self.createDataImpl(allocator: allocator, raw: raw, parent: nil, absoluteInfo: .forRoot(raw))
  }

  deinit {
    // print("nodeCount: \(root.pointee.raw.totalNodes), estimated: \(Self.slabSize(for: root.pointee.raw)), allocated: \(allocator.totalByteSizeAllocated)")
    self.mutex.destroy()
  }

  /// Return the childen data of the given node.
  ///
  /// The layout buffer is created and cached when it's first accssed.
  func layout(for parent: SyntaxDataReference) -> SyntaxDataReferenceBuffer {
    let childCount = Int(truncatingIfNeeded: parent.pointee.childCount)

    // Return empty buffer for the node with no children.
    guard childCount != 0 else {
      return SyntaxDataReferenceBuffer()
    }

    // The storage to the pointer to the buffer is allocated next to the SyntaxData.
    let baseAddress = parent.advanced(by: 1)
      .unsafeRawPointer
      .assumingMemoryBound(to: SyntaxDataReference?.self)
    let buffer = UnsafeBufferPointer(start: baseAddress, count: childCount)

    // The _last_ element is initially filled with `~0` indicating not populated.
    @inline(__always) func isPopulated() -> Bool {
      baseAddress
        .advanced(by: childCount - 1)
        .withMemoryRebound(to: UInt.self, capacity: 1) { pointer in
          pointer.pointee != ~0
        }
    }

    // If the buffer is already populated, return it.
    if isPopulated() {
      return SyntaxDataReferenceBuffer(buffer)
    }

    mutex.lock()
    defer { mutex.unlock() }

    // Recheck before populating, maybe some other thread has populated the buffer
    // during acquiring the lock.
    if !isPopulated() {
      populateDataLayoutImpl(parent)
    }

    return SyntaxDataReferenceBuffer(buffer)
  }

  /// Fill the layout buffer of the node.
  private func populateDataLayoutImpl(_ parent: SyntaxDataReference) {
    let baseAddress = parent.advanced(by: 1)
      .unsafeRawPointer
      .assumingMemoryBound(to: SyntaxDataReference?.self)

    var ptr = UnsafeMutablePointer(mutating: baseAddress)
    var absoluteInfo = parent.pointee.absoluteInfo.advancedToFirstChild()
    for raw in parent.pointee.raw.layoutView!.children {
      let dataRef = raw.map {
        Self.createDataImpl(allocator: self.allocator, raw: $0, parent: parent, absoluteInfo: absoluteInfo)
      }
      ptr.initialize(to: dataRef)
      absoluteInfo = absoluteInfo.advancedBySibling(raw)
      ptr += 1
    }
  }

  /// Calculate the recommended slab size of `BumpPtrAllocator`.
  ///
  /// Estimate the total allocation size assuming the client visits every nodes.
  /// Return the estimated size, or 4096 if it's larger than 4096.
  ///
  /// Each node consumes `SyntaxData` size at least. In addition to that, each syntax collection
  /// element consumes `SyntaxDataReference` in the parent's layout. For non-collection layout
  /// nodes, the layout is usually sparse, so we can't calculate the exact memory consumption
  /// until we see the syntax kind. But 4 slots per each node looks like an enough estimation.
  private static func slabSize(for raw: RawSyntax) -> Int {
    let dataSize = MemoryLayout<SyntaxData>.stride
    let slotSize = MemoryLayout<SyntaxDataReference?>.stride

    let nodeCount = raw.totalNodes
    var totalSize = dataSize
    if nodeCount > 1 {
      totalSize += (dataSize + slotSize * 4) * (nodeCount &- 1)
    }
    // Power of 2 might look nicer, but 'BumpPtrAllocator' doesn't require that.
    return min(totalSize, 4096)
  }

  /// Allocate and initialize `SyntaxData` with the trailing uninitialized buffer for the references to the children.
  private static func createDataImpl(
    allocator: BumpPtrAllocator,
    raw: RawSyntax,
    parent: SyntaxDataReference?,
    absoluteInfo: AbsoluteSyntaxInfo
  ) -> SyntaxDataReference {
    let childCount = raw.layoutView?.children.count ?? 0

    // Allocate 'SyntaxData' + buffer for child data.
    // NOTE: If you change the memory layout, revisit 'slabSize(for:)' too.
    let totalSize = MemoryLayout<SyntaxData>.stride &+ MemoryLayout<SyntaxDataReference?>.stride * childCount
    let alignment = MemoryLayout<SyntaxData>.alignment
    let allocated = allocator.allocate(byteCount: totalSize, alignment: alignment).baseAddress!

    // Initialize the data.
    let dataRef = allocated.bindMemory(to: SyntaxData.self, capacity: 1)
    dataRef.initialize(
      to: SyntaxData(
        raw: raw,
        parent: parent,
        absoluteInfo: absoluteInfo,
        childCount: UInt32(truncatingIfNeeded: childCount)
      )
    )

    if childCount != 0 {
      // Fill the _last_ element with '~0' to indicate it's not populated.
      allocated
        .advanced(by: MemoryLayout<SyntaxData>.stride)
        .bindMemory(to: SyntaxDataReference?.self, capacity: childCount)
        .advanced(by: childCount - 1)
        .withMemoryRebound(to: UInt.self, capacity: 1) {
          $0.initialize(to: ~0)
        }
    }

    return SyntaxDataReference(UnsafePointer(dataRef))
  }
}

/// ``SyntaxNode`` used to be a pervasive type name in SwiftSyntax that has been
/// replaced by the ``Syntax`` type.
@available(*, unavailable, message: "use 'Syntax' instead")
public struct SyntaxNode {}

/// See `SyntaxMemoryLayout`.
let SyntaxMemoryLayouts: [String: SyntaxMemoryLayout.Value] = [
  "Syntax": .init(Syntax.self),
  "SyntaxData": .init(SyntaxData.self),
  "AbsoluteSyntaxInfo": .init(AbsoluteSyntaxInfo.self),
  "SyntaxDataReference?": .init(SyntaxDataReference?.self),
]
