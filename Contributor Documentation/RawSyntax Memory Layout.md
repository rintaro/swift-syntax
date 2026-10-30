# RawSyntax Memory Layout

How a `RawSyntax` node is laid out in memory, and the rules code that builds or reads one has to follow.

## Overview

`RawSyntax` is the immutable tree underneath SwiftSyntax's public `Syntax` API. A parse produces one raw node per token and one per layout node, so how a node is laid out decides how much memory a tree takes and how many instructions it costs to read.

A raw node is not a Swift class or struct. Each node is a single allocation in a ``RawSyntaxArena``: a one-word *header* followed by a *tail*, which holds the fields of one of four *shapes* and whatever variable-length data that shape needs. A node takes only the room its own shape needs, so a short token can be as small as 16 bytes.

The sizes below are for 64-bit platforms. `MemoryLayoutTest` in `Tests/SwiftSyntaxTest` tracks the size, stride and alignment of every type mentioned here. Update its expected values whenever you change one of them.

## The Node

`RawSyntax` is a pointer to the node's header:

```swift
public struct RawSyntax {
  var pointer: ArenaAllocatedPointer<RawSyntaxData>
}
```

The header is a `RawSyntaxData`, an enum with four cases, each of which carries the arena that owns the node:

```swift
enum RawSyntaxData {
  case smolParsedToken(RawSyntaxArenaRef)
  case parsedToken(RawSyntaxArenaRef)
  case materializedToken(RawSyntaxArenaRef)
  case layout(RawSyntaxArenaRef)
}
```

`RawSyntaxArenaRef` is an unretained (`Unmanaged`) class reference, and the enum's case is stored in the reference's spare bits, so the whole header is one word. The case says which shape's fields begin at the start of the tail, immediately after the header (`RawSyntax.tailOffset`):

```
RawSyntax.pointer
|
v
+-----------------------+---------------------+-----------------------+
| header: RawSyntaxData | fields of the shape | variable-length data  |
| (arena ref + case)    | the header names    | (text or child slots) |
| 8 bytes               |                     |                       |
+-----------------------+---------------------+-----------------------+
                        |<------------------ tail ------------------->|
```

Every node is aligned to ``RawSyntaxArena/nodeAlignment`` (8 bytes), so the header and the fields of every shape must need no more alignment than that. `RawSyntax.allocate` asserts it.

Read a node's fields through the accessor for its shape: `asSmolParsedToken`, `asParsedToken`, `asMaterializedToken` or `asLayout`. Each traps if the header names another shape. Where the shape isn't known, switch over `header`, or use the higher-level `RawSyntaxTokenView` and `RawSyntaxLayoutView`.

## Tokens

A token has one of three shapes. Tokens made from source text, as the parser makes them, use one of the two parsed shapes. The third is for tokens built from Swift values, such as `TokenSyntax.identifier("foo")`, and for tokens given explicit trivia pieces rather than trivia text.

### Short Parsed Token

```
+--------+---------------------------------+--------------------+
| header | SmolParsedToken (4 bytes)       | whole text, padded |
|        | wholeTextLength  textLowerBound |                    |
|        | textUpperBound   tokenKind      |                    |
|        | (UInt8 x 4)                     |                    |
+--------+---------------------------------+--------------------+
```

Most tokens in a file are present, carry no diagnostic, and have a *whole text*, meaning the token's text plus its leading and trailing trivia, of at most 255 bytes. For those, `RawSyntax.parsedToken` uses `SmolParsedToken`, which holds every length in a byte. The shape itself implies that the token is present and has no diagnostic.

`textLowerBound` and `textUpperBound` give the range of the token's own text within the whole text. What comes before that range is leading trivia, and what comes after it is trailing trivia.

### Parsed Token

```
+--------+--------------------------------------+--------------------+
| header | ParsedToken (20 bytes)               | whole text, padded |
|        | wholeTextLength  textLowerBound      |                    |
|        | textUpperBound   (UInt32 x 3)        |                    |
|        | tokenDiagnostic  tokenKind  presence |                    |
+--------+--------------------------------------+--------------------+
```

Any other parsed token, such as a missing token, one with a diagnostic, or one whose whole text exceeds 255 bytes, uses `ParsedToken`. It holds the same three lengths as `UInt32`, plus the diagnostic and the presence.

### Token Text

Both parsed shapes copy the token's whole text into the node, after the fields, so a tree doesn't depend on the source buffer outliving the parse. The text is the last thing in the node, so it is padded to a whole unit: 4 bytes for texts of up to 4 bytes, and 8 bytes otherwise. This lets the text be copied a unit at a time instead of through `memcpy`.

`RawSyntax.textByteCount(for:)` computes the padded size and `RawSyntax.copyText` writes it, and the two must always agree. `copyText` reads whole units from the source only where those bytes still lie inside the buffer being lexed, and copies exactly otherwise.

A parsed token stores its trivia only as text. Trivia pieces are parsed lazily, when a client asks for them, through the trivia-parsing function of the ``ParsingRawSyntaxArena`` that owns the node. So a parsed token must always be allocated in a `ParsingRawSyntaxArena`.

### Materialized Token

```
+--------+---------------------------------------------------------+
| header | MaterializedToken (56 bytes)                            |
|        | tokenKind  tokenText: SyntaxText  triviaPieces: buffer  |
|        | numLeadingTrivia  byteLength  presence  tokenDiagnostic |
+--------+---------------------------------------------------------+
                        |                      |
                        v                      v
           text interned in the arena   RawTriviaPiece buffer in the arena
```

A materialized token has no tail data. Its text and trivia pieces are separate allocations in the same arena, which `tokenText` and `triviaPieces` point to. `RawSyntax.materializedToken` interns the text into the arena, unless it is the token kind's static default text, so the token never refers to memory that might not outlive it.

## Layout Nodes

Layout nodes and collections share one shape. A 16-byte `Layout` is followed by the node's *slots*, one `RawSyntax?` (8 bytes) each:

```
+--------+-----------------------------------+-----------------------+
| header | Layout (16 bytes)                 | slots: RawSyntax? x N |
|        | childCount  byteLength  nodeCount |                       |
|        | (UInt32 x 3)                      |                       |
|        | kind  recursiveFlags  storage     |                       |
+--------+-----------------------------------+-----------------------+
```

- `childCount` is the number of *real* children: the children a node's kind names, not counting `unexpected` slots.
- `byteLength` is the length of the subtree's text, and `nodeCount` is the number of nodes in the subtree, including the node itself. `makeLayout` sums both from the children with checked arithmetic.
- `recursiveFlags` summarizes the subtree: whether it contains errors, warnings or a `SequenceExprSyntax`, and whether the parse hit its maximum nesting level.
- `storage` says how the slots hold the children.

### Storage

A layout node's kind describes its children with an `unexpected` slot before the first child, between every pair, and after the last, so `n` children take `2n + 1` positions. In practice almost every `unexpected` slot is empty, so a node keeps room for those slots only when one of them is occupied:

| `storage` | used for | slots |
|---|---|---|
| `.flat` | collections, and the layout kinds that don't interleave `unexpected` slots | `childCount` slots, every one non-nil |
| `.layout` | a kind that interleaves, where every `unexpected` slot is empty | the `childCount` real children |
| `.layoutWithUnexpected` | a kind that interleaves, where at least one `unexpected` slot is occupied | the `childCount` real children, then all `childCount + 1` `unexpected` slots |

Real children always come first, whatever the storage. So the `k`th real child is always slot `k`, and reaching it never depends on the storage:

```
 Tree's view of a node with 3 children (u = unexpected, c = real child):

     u0  c0  u1  c1  u2  c2  u3

 .layout:                  [ c0 | c1 | c2 ]
 .layoutWithUnexpected:    [ c0 | c1 | c2 | u0 | u1 | u2 | u3 ]
```

`SyntaxKind.interleavesUnexpectedChildren`, which is generated, says whether a kind interleaves. A node's storage must agree with it: `.flat` exactly when the kind doesn't interleave. `makeLayout` asserts that, and that a `.flat` node has no nil slot.

### Building a Layout Node

There are two `makeLayout` entry points:

- `makeLayout(kind:childCount:storage:…)` is for a caller that knows the real-child count and the storage up front. The generated raw initializers know statically whether their kind interleaves, check whether any `unexpected` argument is non-nil, and write each slot exactly once where it lives.
- `makeLayout(kind:uninitializedCount:…)` takes the children as the tree describes them, `unexpected` slots included. It writes them into a temporary, decides the storage from what was written, and lays them out in the node. Every operation that edits a node goes through this form, so an edited node is always as compact as its contents allow.

The first form is `@inline(__always)`, because every layout node in a parse is built through it.

### Reading a Layout Node

Pick the reader that matches what you need:

- `RawSyntaxLayoutView.realChild(at:)` and `unexpectedSlot(at:)` reach one child by where it sits. The generated raw accessors use them with constant indices. `realChild(at:)` is a single load. `unexpectedSlot(at:)` tests the storage once and returns `nil` for a node that kept no room for `unexpected` slots.
- `RawSyntaxLayoutView.elements` reads a collection's children as non-optional `RawSyntax`.
- `RawSyntax.forEachChildInSourceOrder(_:)`, `firstChildResultInSourceOrder(_:)` and `lastChildResultInSourceOrder(_:)` visit the children a node holds, in source order, without stepping through absent `unexpected` positions.
- `RawSyntaxLayoutView.children`, a `RawLayoutChildren`, presents the children as the tree describes them, with every `unexpected` position and `nil` for those the node kept no room for. Mapping a position to a slot costs a branch and a division, so use it only when you need positions, for example to rebuild a node or to index into the kind's structure.

## The Arena

A ``RawSyntaxArena`` owns every node allocated in it, together with the interned text and trivia buffers of materialized tokens. It allocates from slabs with a `BumpPtrAllocator`. Nodes aren't reference-counted and are never freed individually: everything goes when the arena does.

- A `ParsingRawSyntaxArena`, which every parse allocates into, sizes its slabs for the source it will hold. It starts from 4 KB and doubles up to the source's size, with a 4 MB maximum. It also holds the trivia-parsing function that parsed tokens need, and the lookahead lengths an incremental reparse reads.
- A node refers to its arena through the header's unretained `RawSyntaxArenaRef`, so reading a node involves no reference counting. Code that holds a `RawSyntax` must keep its arena alive some other way. The `Syntax` layer does so from its root, and `RawSyntax.arena` returns a `RetainedRawSyntaxArena` for code that holds a raw node directly.
- A layout node can have children from another arena, for example after an edit. `makeLayout` then calls `addChild`, so the node's arena retains the child's arena until it is itself freed.

## The Syntax Layer on Top

The public `Syntax` API wraps raw nodes in `SyntaxData`, which records a node's parent and absolute position. `SyntaxData` values live in a separate `SyntaxDataArena`, owned by the tree's root, and are created lazily: a node's children get their `SyntaxData` the first time one of them is reached. A `SyntaxData` with children has one extra word after it, an atomic pointer to its *layout buffer*. That buffer holds one `SyntaxDataReference?` per position the kind names, `unexpected` slots included, so the indices clients use to reach a child don't depend on the raw node's storage.

## Changing the Layout

- Keep `MemoryLayoutTest` up to date.
- Every shape's fields need at most ``RawSyntaxArena/nodeAlignment`` of alignment, and so do a layout node's slots, which start right after `Layout`.
- `textByteCount(for:)` and `copyText` must agree on how much room a token's text takes. `syntaxTextBytes` relies on the same padding.
- Real children come first in a layout node's slots, whatever its storage. The generated accessors' constant indices depend on it.
- A `.flat` node never has a nil slot, and a node's storage always agrees with `interleavesUnexpectedChildren`.
- Run the tests with `SWIFTSYNTAX_ENABLE_RAWSYNTAX_VALIDATION` set as well. It validates every layout node's children against its kind as it is built.
