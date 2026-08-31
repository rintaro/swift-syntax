# Compacting the `unexpected` slots out of layout nodes

Branch `perf-compact-layout-nodes`, off `perf-parser-2026-woc` (`dc3f8ed82`).

A non-collection layout node interleaves an `unexpected` slot before its first
child, between every pair, and after the last: *n* children occupy 2*n*+1 slots.
Those slots are **56.8% of every layout child slot in the tree** and, in code
that parses without error, none of them holds anything.

The proposal is to give a node that has no unexpected children a tail holding
only its real children, and to say which shape a node has in the header enum
that every reader already switches on.

---

## What was measured

Walking every layout node of the raw tree, over the 749 Swift files in
`swift-syntax-mono/swift-syntax` (9,637,680 source bytes):

| | |
|---|---|
| nodes | 2,802,769 — 1,132,225 layout, 437,330 collection, 1,233,214 token |
| child slots | 8,360,911 in layout nodes, 420,213 in collections |
| of the layout slots, `unexpected` | 4,746,568 — **56.77%** |
| occupied `unexpected` slots | **0** |

Occupancy under damage, to see whether the compact form is a fair-weather
optimization. Truncating each file to 70% of its bytes leaves constructs
unterminated; deleting every 200th byte corrupts pervasively:

| corpus | layout nodes | carrying any unexpected |
|---|---|---|
| valid Swift | 1,132,225 | 0 (0.00%) |
| truncated to 70% | 767,269 | 17 (0.002%) |
| every 200th byte deleted | 1,040,498 | 5,848 (0.56%) |

Truncation produces *missing* tokens rather than unexpected ones, which is why it
barely registers. Even under the corruption that does produce them, more than
99.4% of layout nodes would still take the compact form.

### Estimated saving

At 8 bytes a slot, against the tree sizes in `PERFORMANCE-REPORT.md`:

| input | tree now | droppable | after | change |
|---|---|---|---|---|
| `MinimalCollections.swift.input` | 15.32× source | 4.11× | 11.21× | **−26.8%** |
| concatenated generated sources | 13.95× | 3.51× | 10.44× | **−25.2%** |
| `nonascii_heavy.swift.input` | 15.31× | 4.12× | 11.19× | **−26.9%** |
| 749-file corpus | — | 3.94× (37,972,544 bytes) | — | — |

Time improves too, by 1.5% to 1.7% — see *The write path* for why, which is not
the reason given here:
`makeLayout` writes *n* slots rather than 2*n*+1 and its
`byteLength`/`descendantCount`/`recursiveFlags` loop iterates less than half as
many. `4d63b3595` established that slot writes on this path are worth whole
percentages.

---

## The structure this relies on

`interleaveUnexpectedChildren` in
`CodeGeneration/Sources/SyntaxSupport/Node.swift` produces
`[U, c₀, U, c₁, …, U]`, so for an interleaved node:

- `unexpected` slots are exactly the **even** logical indices, real children the
  odd ones,
- logical child count is always **2*n*+1**, hence always odd.

Verified over the corpus: no layout kind had an even child count, and no even
slot ever held a node whose kind was not `unexpectedNodes`. The largest layout
node has 23 children; the common counts are 7, 5, 9, 3, 13, 11.

Two exceptions, both from `Node.swift:145`
(`(kind.isBase || noInterleaveUnexpected) ? children : interleaveUnexpectedChildren(children)`):

- **Collections** are flat. Their children are all real, and there are 437,330 of
  them in the corpus.
- **`unexpectedCodeDecl`** (`CommonNodes.swift:415`) opts out. Its single child
  *is* an `UnexpectedNodesSyntax`, as a real child rather than an interleaved
  slot.

So "even index means `unexpected` slot" must never be inferred from an index. It
has to come from the node.

A third measured fact shapes the design: **no collection child is ever nil** —
420,213 slots, zero nil.

> The occupancy probe assumed parity, so a few of the 5,848 nodes in the
> corrupted run were `unexpectedCodeDecl` carrying its real child rather than an
> interleaved slot. The conclusion is unaffected; the exact figure is a slight
> over-count.

---

## Design

### Shape lives in `RawSyntaxData`, not in a flag

```swift
internal enum RawSyntaxData {
  case smolParsedToken(RawSyntaxArenaRef)
  case parsedToken(RawSyntaxArenaRef)
  case materializedToken(RawSyntaxArenaRef)
  case collection(RawSyntaxArenaRef)            // tail: [Collection][RawSyntax × n]
  case layout(RawSyntaxArenaRef)                // tail: [Layout][RawSyntax? × n]
  case layoutWithUnexpected(RawSyntaxArenaRef)  // tail: [Layout][RawSyntax? × n][RawSyntax? × n+1]
}
```

The enum is the word every reader already switches on to reach a tail, so shape
costs nothing to store and nothing to test. Cases are free: an enum over an
8-byte-aligned class reference holds up to 128 of them in one word.

Three reasons to prefer this to a bit in `Layout`:

1. **A forgotten case is a compile error; a forgotten bit test is a wrong
   memory read.** The failure mode of this change is reading a tail under the
   wrong interpretation. There are 31 sites switching on the discriminator, in
   `Raw/RawSyntax.swift`, `Raw/RawSyntaxLayoutView.swift`,
   `Raw/RawSyntaxTokenView.swift` and `SourceLocation.swift`; the compiler will
   list them.
2. **A collection's tail can be `RawSyntax` rather than `RawSyntax?`.** Nothing
   is ever nil there, and the generated collection initializer already holds
   non-optional values — it writes `ptr.initialize(to: elem.raw)` from a
   `RawSyntaxNodeList` and only widens because the buffer is typed that way.
   Element iteration loses its nil test.
3. **Growing back to the full form becomes a case change** rather than clearing
   a bit, so a mutation that writes an unexpected child cannot forget.

`Layout`'s fields are unchanged. This step alone saves no memory; the saving
comes from which case a node is built as.

### Real children first

Within a layout tail, real children come before the unexpected region:

```
.layout                 [c₀ c₁ … c(n-1)]
.layoutWithUnexpected   [c₀ c₁ … c(n-1)] [u₀ u₁ … uₙ]
```

Real child *k* is then at physical index *k* in **both** cases, so the accessors
that dominate every read — `.name`, `.body`, `.signature` — stay unconditional
constant-index loads. Had the tail kept source order, a real-child accessor
would have to choose between `k` and 2*k*+1 and would need a shape test on the
hottest path in the library.

What it costs: in the full form, physical order no longer matches source order,
so every order-sensitive consumer must go through the logical view rather than
the buffer. Order-*independent* consumers are unaffected —
`byteLength`/`descendantCount`/`recursiveFlags` are sums over non-nil children.

### Where the mapping lives

- **Generated accessors need no mapping.** The generator knows which children
  are unexpected, so it emits the physical constant: real child *k* is
  `base[k]`, and an unexpected accessor is `nil` for `.layout` and `base[n + j]`
  for `.layoutWithUnexpected`. That covers 1,798 raw accessor sites and 3,596
  syntax accessor sites, none of which needs arithmetic and only the unexpected
  ones of which need to know the case.
- **Dynamic paths switch once per node, never per child.** The logical view is a
  concrete struct — never `any` — and the shape switch is hoisted out of loops,
  leaving one of three straight loops:
  - `.collection`: walk the tail; elements are non-optional.
  - `.layout`: walk the *n* real children, emitting a nil before each and one at
    the end. No per-element branch, and no read of slots that do not exist.
  - `.layoutWithUnexpected`: interleave `base[0..<n]` with `base[n...]`.

  The logical sequence produced is byte-identical to today's, which is what
  keeps `absoluteInfo`, `layoutIndexInParent` and the rewriter untouched.

### The invariant that keeps callers honest

**Every node-building entry point decides the case by inspecting what it was
given; none of them takes the case as a parameter.** `makeLayout`,
`replacingLayout(with:)`, `replacingChild(at:)`, `insertingChild` and the
`withX` setters all scan the would-be unexpected slots and emit `.layout` when
they are all nil.

That single rule is what makes the rest of the library need no changes, and in
particular it is what stops a rewritten tree from silently reverting to the
expanded form.

---

## Consumers, and what each needs

| consumer | what it does today | needed |
|---|---|---|
| generated raw accessors (1,798) | `layoutView.children[N]` | regenerate with physical constants |
| generated syntax accessors (3,596) | `child(at: N)`, `replacingChild(at: N)` | regenerate with physical constants |
| `Syntax.createLayoutDataImpl` | the one loop that walks raw children in source order, once per node, memoized | switch on case, three concrete loops |
| `SyntaxChildren` | iterates the Syntax layer's `SyntaxDataReferenceBuffer`, not raw children | **nothing** |
| `SyntaxRewriter.visitChildren` | copies `layoutView!.children` into a scratch buffer, writes at `layoutIndexInParent`, calls `replacingLayout(with:)` | **nothing**, provided `replacingLayout` re-detects the case |
| `RawSyntaxLayoutView` mutation | `replacingChild`/`insertingChild`/`removingChild` shared between collections and layouts | split by shape; re-detect the case |
| `formLayoutArray()`, `description`, `SourceLocation` | iterate `children` in order | logical view, switch hoisted |
| generated `RawSyntaxValidation` | validates against logical arity | logical view |

`SyntaxRewriter` deserves a note because it looks like a problem and is not: it
uses no per-kind indices, so it is correct under any shape. The risk it carries
is that every node it rebuilds would come back expanded, which is exactly what
the re-detection invariant prevents.

---

## Staging

Each step is independently reviewable, and each has something to measure.

1. **Add `.collection`.** Done — `c09a35f68`. The case split alone, with both
   cases still holding the same fields and the same tail, so no memory changes
   and the parsed output is identical. Measured within noise on all three inputs.
   Non-optional collection tails are deferred to a step of their own, since they
   are a representation change rather than a discriminator change.
2. **Split `.layout` / `.layoutWithUnexpected`, compacting at construction,**
   and implement re-detection in every building entry point. This is where the
   ~26% lands. Measure tree memory and time.
3. **Regenerate the accessors** against physical indices.
4. **Mutation paths**: converting case when an unexpected child is written, with
   tests written directly against it.
5. **Non-optional collection tails.** Nothing is ever nil there, so element
   iteration can lose its nil test.

Steps 2 and 4 must land together — step 2 without step 4 is unsound.

### Two things step 1 taught, which step 2 should apply first

**The exhaustive switches are the safe ones; the `default:` arms are the
hazard.** The compiler listed 26 switches to extend, and every one of them was
mechanical. What it could not list were the four checked accessors —
`smolParsedToken`, `parsedToken`, `materializedToken`, `layout` — each of which
ends in `default: preconditionFailure`. Three of them correctly reject a
collection, but `layout` would have trapped on every collection node in the
tree, and nothing said so. **Convert those four to exhaustive switches before
adding more cases**, so that the compiler covers them too.

**Let one place decide, by inspecting what it was given.** The plan proposed a
`DEBUG`-only assertion that `kind.isSyntaxCollection` agreed with the case. That
turned out to be unnecessary: deriving the case from the kind at the single site
that allocates a node means there is no second source of truth to check. Step 2
cannot do exactly that — whether a node is compact depends on its arguments, not
its kind — but it can keep the discipline: every building entry point decides for
itself by looking at the unexpected slots it was handed, and none of them accepts
the shape as a parameter.

### The write path, for step 2

The initializer closure `makeLayout` takes writes the *logical* layout, so
whether the unexpected slots are all nil is not known until it has run — after
the allocation size would have had to be chosen. Two ways out:

- **Fill a scratch buffer, then allocate.** A layout node has at most 23 slots,
  so the scratch is 184 bytes of `withUnsafeTemporaryAllocation`. Scan it, then
  allocate the exact size and copy. Costs one extra pass of at most 23 words per
  node, and requires no change to any caller or to the generated code.
- **Have the generator hand over the two groups separately,** so the shape is
  known before allocating and nothing is copied twice. No scratch, no extra
  write, but it changes the template and every generated initializer.

Both were built. **The copy was never the cost, and a `memset` was.**

The scratch lowers to a stack allocation with no runtime call — neither binary
references `swift_stackAlloc` — and `makeLayout` inlines into every caller, so it
never appears as a profile leaf. The extra stores land in hot memory while the
cold traffic, first touch of freshly bump-allocated arena memory, is identical
either way. The two versions measured alike.

What made the second version lose at first was that handing the closure a buffer
into arena memory turned the generated `layout.initialize(repeating: nil)` into a
real `_platform_memset` — 1.95% of a parse — which cannot be eliminated because
the compiler cannot see that every slot is later written. Every slot *is* written
exactly once, since the `unexpected` slots exist only when they are being
written, so the generated initializer initializes each slot instead of blanking
the tail and assigning over it. With that, parsing is 1.5% to 1.7% *faster* than
before the compaction rather than 0.2% to 1.5% slower.

The blanket initialize predates this work, so part of that gain is a `memset`
every node has been paying for and did not need.

**Knowing which kinds interleave cannot come from parity.** `unexpectedCodeDecl`
has one child, at index 0, and that child is real — so an odd child count does
not imply the even slots are unexpected. The schema knows
(`noInterleaveUnexpected`, `kind.isBase`), so the generator should emit the
answer as a property on `SyntaxKind` rather than have the runtime infer it or a
hand-written list drift from it.

---

## Verification

The instruments this branch already relies on, in the order they catch things:

- **Differential fingerprint over the 749-file corpus** — tree shape, trivia,
  error status and round-trip fidelity, compared against the branch point. A
  mapping mistake shows up here immediately.
- **46 trivia cases, 26 UTF-8 cases, the incremental-reuse invariants.**
- **Address Sanitizer**, because this is pointer arithmetic on a tail: the
  corpus, the malformed inputs, and the exactly-sized-allocation sweep in
  `testParseBufferEOFEdgeCases`.
- **Memory measured as what the allocator's bump pointer advances by**, padding
  included — not `totalByteSizeAllocated`, which ignores inter-allocation
  padding and understates the branch.
- No assertion that the kind and the case agree: construction derives one from
  the other, so there is nothing to disagree. Where a shape *cannot* be derived
  from the kind — compact against full — the rule is that every building entry
  point decides for itself from what it was handed.

Step 4 wants its own direct test rather than relying on the corpus: set an
unexpected child on a compacted node, round-trip it, and compare
`formLayoutArray()` against the equivalent node built expanded.

---

## Risks and open questions

- **`layoutView` and `children` are `@_spi(RawSyntax) public`,** and clients
  index and iterate them — ASTGen in the compiler, sourcekit-lsp. `children`
  must keep working for all three cases, and its type changing from
  `RawSyntaxBuffer` to a view is a source break worth checking against those two
  before step 1 rather than after.
- **`Layout.childCount`**: keep storing the logical 2*n*+1, or store *n* and
  derive? Storing *n* makes the allocation size and the accessor constants match
  the field, at the cost of touching everything that reads it expecting logical
  arity, including generated validation. Undecided.
- **Two sources of truth** for collection-ness, as above.

---

## Considered and rejected

**An occupancy bitmap for the nil real children.** 34.1% of the *real* child
slots are nil — optional children that are absent: 1,232,536 slots over the
corpus, 1.13× / 0.80× / 0.94× of source on the three inputs, so 5% to 7% of tree
memory. Packing the present ones and recording which they are in a bitmap would
collect that.

The bounds favour it, which is why it is written down rather than dismissed. From
the generated schema: the largest logical index is 22, so a layout node has at
most **11** real children; at most **6** of a node's real children are optional
(`RawTupleTypeElementSyntax`, `RawForStmtSyntax`), and **196 of 298 kinds have
none**; only 19.1% of real-child accessors — 210 of 1,100 — return an optional at
all. So the bitmap needs 6 bits, and a `UInt8` fits in the padding byte `Layout`
already has, costing nothing. A naive `UInt32` would have been the trap: it takes
`Layout` from size 15 to 19, pushing the children region off its 8-byte alignment
for 8 bytes a node — 0.94× of source, against the 1.02× being reclaimed.

It is still not worth taking. Mapping a logical index needs a presence test plus a
population count of the bits below it:

```
optional child at ordinal j  →  occupancy & (1 << j) != 0
                                base[requiredCount + popcount(occupancy & ((1 << j) - 1))]
```

Ordering required children first keeps 890 of the 1,100 real-child accessors as
constant-index loads, and the remaining 210 popcount over at most 6 bits with a
constant mask, which the generator can unroll into bit tests rather than
`nonzeroBitCount` — worth doing on arm64, where that crosses to SIMD and back.
Sequential traversal needs no popcount at all; it walks the bits and advances a
pointer.

The deeper objection is not the arithmetic. It is that a node's physical shape
would depend on *which* of its optional children happen to be present, where
compacting the unexpected slots leaves shape decided by the kind alone. That
property is what makes the mapping cheap to reason about, cheap to assert, and
cheap to re-derive on mutation.

---

## Adjacent findings, deliberately out of scope

Each was measured while investigating this and is independent of it.

- **Empty collections are everywhere, and worth about an eighth of this plan.**
  437,330 collection nodes hold 420,213 elements, and **188,625 of them — 43.1%
  — are empty**, because every declaration carries `attributes` and
  `declModifierList` and every call carries
  `multipleTrailingClosureElementList`; those three kinds alone are 175,505 of
  the empty ones. An empty collection costs 24 bytes: 8 of header plus a 16-byte
  `Layout` whose `childCount`, `byteLength` and `descendantCount` are all zero,
  so `kind` is the only field saying anything.

  | variant | per node | corpus | of tree memory, three inputs |
  |---|---|---|---|
  | `.emptyCollection`, allocated, no tail | −16 B | 0.31× source | 2.0% / 1.4% / 3.2% |
  | inline value, no allocation | −24 B | 0.47× | 3.1% / 2.1% / 4.8% |
  | interned per kind per arena | −24 B | 0.46× | ≈ as above |

  Packing `kind` into the header word fits — 11 spare bits, 3 for the case tag,
  far fewer than 64 collection kinds — but it is a hand-rolled encoding rather
  than something the enum layout gives. The inline variant is blocked by
  identity: `RawSyntax.ID` *is* the node's pointer, and `SyntaxRewriter` compares
  it to detect rewrites, so a node with no allocation has no id. Interning keeps
  a pointer but gives every empty list of a kind the same one.
- **The Syntax layer wastes the same 56.8%.** `createLayoutDataImpl` allocates a
  `SyntaxDataReference?` per *logical* slot, so a fully traversed corpus tree
  costs 8.36M refs where 3.6M are meaningful — 67 MB rather than 29 MB. It is
  transient, per `Syntax` arena and only for visited nodes, but it is real for
  traversal-heavy consumers like the formatter. Compacting it is gated on what
  `layoutIndexInParent` means, so it must stay separate from the raw-side
  change.
