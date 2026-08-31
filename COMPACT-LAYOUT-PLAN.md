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

## Where it got to

| | |
|---|---|
| tree memory | 15.32× → **11.20×**, 13.95× → **10.44×**, 15.31× → **11.20×** of source |
| parse time | **1.5% to 1.7% faster** |
| reading a tree through its typed accessors | 45,786,168 → **42,788,446** instructions, **6.5% fewer**, over the four commits that followed the compaction |

Verified at each step against a 749 file corpus and 120 deliberately corrupted
files, with Address Sanitizer clean on both, and the suite at 3,490 passing.

Almost all of the read-path gain came from a single pattern: **not asking
`SyntaxKind` a question the header already answers.** Both `isSyntaxCollection`
and `interleavesUnexpectedChildren` are switches over some three hundred kinds,
and they were sitting on paths that run per node.

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
  case flat(RawSyntaxArenaRef)                  // tail: [Layout][RawSyntax? × n], none absent
  case layout(RawSyntaxArenaRef)                // interleaved, compact: [Layout][RawSyntax? × n]
  case layoutWithUnexpected(RawSyntaxArenaRef)  // [Layout][RawSyntax? × n][RawSyntax? × n+1]
}
```

`.flat` is every collection and the few layout kinds that opt out of
interleaving: children one after another, every slot filled. Splitting it from
`.collection` was tried and merged back, because the two described the same
memory and the same guarantee — see the staging notes.

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
2. **A collection's elements can be read as `RawSyntax` rather than
   `RawSyntax?`.** Nothing is ever nil there, so element iteration loses its
   test. Measured at 0.83% of a traversal — but only when the shape question goes
   to the header; see step 5. The storage stays `RawSyntax?`, since an optional
   `RawSyntax` is already one word and changing the tail's type would save no
   memory at all.
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

1. **Add `.collection`.** Done — `f89090804`, with `be5232589` making the checked
   field accessors exhaustive so that a later shape cannot slip past them.
2. **Split `.layout` / `.layoutWithUnexpected`, compacting at construction.**
   Done — `716127f54`, on top of `e7474384d` which generates whether a kind
   interleaves. Tree memory 15.32× → 11.20×, 13.95× → 10.44×, 15.31× → 11.20×.
   `bb1f9a521` then moved the write into the tail; see *The write path*.
3. **Accessors on physical slots.** Done — `0f3933e09`. Reading a tree through
   its typed accessors takes 4.1% fewer instructions.
4. **Mutation paths.** The behaviour landed with step 2 rather than separately:
   every mutating operation on `RawSyntaxLayoutView` builds a layout in the shape
   the tree describes and hands it back to `makeLayout`, which re-examines it, so
   a node that gains an unexpected child becomes `.layoutWithUnexpected` and one
   that loses its last one becomes `.layout` again. Nothing has to remember to
   preserve a shape, which is why `SyntaxRewriter` needed no changes.

   **Its dedicated test is still outstanding.** What covers it today is indirect:
   the suite, and 120 corrupted files that produce and read
   `.layoutWithUnexpected` nodes. Neither aims at the transition itself, and no
   test names `insertingChild`, `replacingChild` or the `withX` setters. The test
   the plan asked for — set an unexpected child on a compact node, round-trip it,
   and compare `formLayoutArray()` against the same node built expanded — should
   be written before this branch is considered finished.
5. **Collection elements read without a test for an absent one.** Done —
   `38b413ab8`. The traversal takes 0.83% fewer instructions.

   Framed here as making the tail non-optional, which turns out to save nothing:
   `RawSyntax?` is already one word, so the tail is the same size either way. What
   there was to win was the branch, and winning it depended on asking the *header*
   whether a node is a collection. Asking `kind.isSyntaxCollection` instead
   measured **+0.06%** — a switch over every kind costs about what a
   well-predicted test per element saves. That is the case split of step 1 paying
   for itself, and the reason to keep `.collection` as a case even though it is
   physically identical to `.layout`.

   `SyntaxCollection.count` followed — `896f90f7b`, another 0.40% — because it
   asked the logical view for a length, and the logical view was built by asking
   the kind whether it interleaves. The generated raw `elements` accessor is still
   on the logical path and allocates an `Array`, so it is probably not worth
   moving.
6. **One flat case, not two.** `.collection` and a flat layout node described the
   same memory and the same guarantee: a collection's fullness comes from its
   category, `unexpectedCodeDecl`'s from its one child being non-optional. Merged
   into `.flat` — `9eb24622b` — with the assertion widened from collections to
   every flat node.

   This turned out to be the largest read-path win, **5.58%**, and not for tidiness:
   with the cases merged, `.layout` means interleaved and compact without
   qualification, so `RawLayoutChildren` takes `interleaves` from the case instead
   of from `kind.interleavesUnexpectedChildren` — a switch over every kind, which
   had been running on every access to a node's children. `makeLayout` stops
   asking `isSyntaxCollection` as well.

   Which reverses what step 5's notes concluded. The measured argument for keeping
   `.collection` as its own case was real, but it was an argument for asking the
   *header* rather than the kind, and merging serves that better than splitting.

Steps 2 and 4 had to land together, and did: step 2 without re-detection would
have let any rewritten node fall back to the expanded shape.

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
- **Instruction counts, repeated, first run discarded.** `AccessorPerformanceTests`
  counts instructions rather than time, which is what makes sub-percent effects on
  the read path measurable at all. But the first run after a build is 5% to 12%
  high from cold caches; warm runs agree to within 0.1% to 0.8%. A single sample
  is worthless here, and one cold sample mixed into a comparison inverted a result
  during this work. Repeat, drop the first, quote the median and the spread.

  Repeated on an idle machine, the single-sample figures held their direction and
  lost about a quarter of their size: 0.83% became **0.63%** (`38b413ab8`), 0.53%
  became **0.40%** (`896f90f7b`), and 5.94% became **5.58%** (`9eb24622b`). Warm
  spread across those runs was 0.06% to 0.37%. The commit messages still quote the
  single samples.
- No assertion that the kind and the case agree: construction derives one from
  the other, so there is nothing to disagree. Where a shape *cannot* be derived
  from the kind — compact against full — the rule is that every building entry
  point decides for itself from what it was handed.

All of the above ran on each of steps 1 to 3: fingerprints identical over the 749
file corpus and over 120 deliberately corrupted files, 107 of which have errors
and so exercise `.layoutWithUnexpected`; the trivia, UTF-8 and incremental
checks identical; Address Sanitizer clean on both corpora.

**The sanitizer run is not a fingerprint oracle against release output.** Two of
the 749 files parse differently in a debug build than in a release one — one
reports an error and 18,494 nodes where release reports none and 18,578 — and they
did so before this work as well as after. Compare an instrumented build against
another instrumented build, never against a release one; that comparison is what
confirmed step 3, and it was identical.

Step 4 still wants its own direct test, as above: set an unexpected child on a
compact node, round-trip it, and compare `formLayoutArray()` against the same
node built expanded. The suite passing is not that test.

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
