# SwiftParser performance work — 2026-08

Branch `perf-parser-2026-woc`, off `main` (`a3cd836bf`).
Commit hashes below are as of writing; rebasing the branch will change them,
so the subject lines are the stable reference.

**Parsing is 2.5 to 2.8 times faster, and the tree it produces is 42% smaller**,
with no change to the parsed output.

| input | main | branch | |
|---|---|---|---|
| `MinimalCollections.swift.input` (177 KB) | 4.906 ms | 1.759 ms | **2.79×** |
| concatenated generated sources (468 KB) | 11.977 ms | 4.639 ms | **2.58×** |
| `nonascii_heavy.swift.input` (321 KB) | 7.998 ms | 3.171 ms | **2.52×** |

| tree memory | main | branch | |
|---|---|---|---|
| `MinimalCollections.swift.input` | 26.45× the source | **15.32×** | −42.1% |
| concatenated generated sources | 24.32× | **13.95×** | −42.6% |
| `nonascii_heavy.swift.input` | 26.87× | **15.31×** | −43.0% |

Interleaved A/B, 20 rounds, two independent builds per side, medians and
minimums agreeing to within 0.02×. Tree memory is what the arena's allocations
actually advance its bump pointer by, padding included — not
`totalByteSizeAllocated`, which ignores the padding between allocations and
understates the branch by about 1.3× of the source.

**On the inputs.** Two of the three are reproducible: `MinimalCollections` ships
in `Tests/PerformanceTest/Inputs`, and `nonascii_heavy` is 700 repetitions of a
struct whose identifiers, literals and doc comments are CJK, emoji and combining
marks — 60% non-ASCII bytes. The declaration-heavy input is
`Sources/SwiftSyntax/generated/*.swift` concatenated in sorted order to 468 KB.
An earlier 317 KB declaration-heavy file was used for most of the per-commit
figures below and has since been lost, so those figures are historical: they were
measured, but not against a file that still exists. Anything re-measured after
that point says which input it used.

---

## How this started, and what it turned out to be

The premise was that copying `Lexer.Cursor` — a large struct copied per token —
was the bottleneck. That was right about the location and wrong about the
mechanism, in a way that took several measurements to pin down.

The profile did not support it: struct copying was 6th by self time at 6.5%,
behind keyword recognition, trivia lexing and spec-set construction. What
settled it was padding `Cursor` by 32 bytes and re-measuring: **+11% parse
time**. Copies were expensive but almost entirely *inlined into their callers*,
so they never appeared as `memmove`.

That produced a rule that held for the rest of the work:

| copy pattern | cost | how it was established |
|---|---|---|
| read-only local snapshot, only some fields used | **free** | converting `nextToken`'s positional snapshots to pointers changes the emitted code by one instruction: 415 → 414, with one more memory op and a frame 16 bytes larger |
| unused by-value parameter | **free** | removing two dead `cursor:` parameters: **+0.4%** |
| snapshot mutated, then written back to `self` | **real** | restructuring `lexTrivia`: **−9.8%** |
| escapes into a returned value | **real, and proportional to its size** | `Cursor` is stored into every `Lexeme`; taking it from 81 bytes to 32 is most of this report |
| a single reference-counted field in a copied struct | **real, and out of proportion** | `unowned(unsafe)` on one 8-byte field: **−4.0%** |

The optimizer reduces a non-escaping read-only snapshot to just the fields
actually touched. Copies cost when the compiler must keep both original and
copy live, or when a field forces a non-trivial copy.

`nextToken` is the clearest illustration, because it contains both kinds side by
side. `leadingTriviaStart`, `textStart` and `trailingTriviaStart` are each a
whole `Cursor` copied off `self`, and each is read only for its
`input.baseAddress` — so SROA splits all three and keeps one pointer apiece.
Spelling that out by hand (`let textStart = self.pointer`) emits the same code.
`let cursor = self` on the line above them looks identical and is not: it is
stored into the returned `Lexeme`, so it escapes and is a real per-token store.
That one copy is why the struct-size commits below were worth ~14% between them,
and why taking `Cursor` out of `Lexeme` is in the rejected table rather than
done.

The last row is the one worth remembering. Removing **72 bytes** of value data
from `LexemeSequence` was worth 1.1–1.8%. Removing **one 8-byte strong
reference** from it was worth 4.0% — because that field was what made the whole
struct non-trivial, turning every lookahead into an outlined copy plus a retain
and every discard into a release.

---

## Where the time went

Self time on the 177 KB input, normalized to absolute cost per parse, because
shares alone mislead when the total more than halves. Both columns are profiled
at the same time with the same grouping, so they are comparable to each other;
the grouping itself is by symbol name and therefore approximate.

| cluster | main | branch | change |
|---|---|---|---|
| Unicode decode / classify | 0.337 ms | 0.011 ms | **−97%** |
| TokenSpec / spec sets | 0.213 | 0.016 | **−92%** |
| Trivia lexing | 0.561 | 0.062 | **−89%** |
| Keyword recognition | 0.503 | 0.078 | **−84%** |
| Reference counting | 0.160 | 0.047 | **−71%** |
| Identifier lexing | 0.374 | 0.121 | **−68%** |
| Arena / allocation | 0.326 | 0.197 | **−40%** |
| Lexer dispatch | 0.569 | 0.386 | −32% |
| **whole parse** | **4.764** | **1.849** | **−61%** |

Lexer dispatch is the least improved and is now the largest cluster, which is
the honest summary of where this branch got to: the work each token costs has
been cut hard, and what is left is the state machine that walks them.

### Struct sizes

| type | main | now |
|---|---|---|
| `Lexer.Cursor` | 81 / 88 | **32 / 32** |
| `Lexer.Cursor.State` | 17 / 24 | **10 / 16** |
| `Lexer.Cursor.StateStack` | 41 / 48 | **8 / 8** |
| `Lexer.Lexeme` | 121 / 128 | **72 / 72** |
| `Lexer.LexemeSequence` | 320 / 320 | **128 / 128** |
| `Parser` | 456 / 456 | **352 / 352** |
| `RawSyntaxData` | 64 / 64 | **40 / 40** |
| `RawSyntaxData.Payload` | 52 / 56 | **32 / 32** |
| `Parser.Lookahead` | 472 / 472 | **224 / 224** |

`Lexer.LexemeSequence` and `Parser.Lookahead` are also now **trivially
copyable**, which the sizes do not show and which is worth more than the bytes.

---

## The commits

Percentages are that commit against its immediate parent, on the two inputs.

### Struct size (Cursor 81 → 48 bytes)

| | |
|---|---|
| `0c3ccd94b` Order `Lexer.Cursor.State` payloads by decreasing alignment | −2.9% / −3.4% |
| `14d54bd0a` Pass the source buffer start as a pointer, not a `Cursor` | −1.1% / −1.8% |
| `6e5ee4ee4` Store the lexer state stack as a pointer and a 32-bit count | −6.0% / −5.5% |
| `1a39c55bc` Drop `languageFeatures` from `Lexer.Cursor` | −4.2% / −3.9% |

Swift does not reorder enum payload fields, so
`inStringLiteral(kind: StringLiteralKind, delimiterLength: Int)` put a 1-byte
enum ahead of an `Int` and padded out to a 16-byte payload where 9 sufficed.
`Optional<UnsafeBufferPointer<State>>` needs 17 bytes, not 16, because
`baseAddress` is already optional and leaves no spare bit for the outer tag.
Dropping `languageFeatures` freed 16 bytes rather than 8, because the three
single-byte optionals that followed then packed into `Position`'s tail padding.

### Keyword identity

| | |
|---|---|
| `41a10b37b` Don't declare attribute names as keywords | neutral |
| `265f0b27e` Resolve a lexeme's keyword once, in the lexer | **−10.3% / −9.8%** |
| `d64f96239` Match declaration token spec sets on the resolved keyword | **−9.8% / −7.8%** |
| `eca3c7bef` Generate token spec sets as switches over kind and keyword | −0.3% / −0.3% |
| `c2a9dffe8` Match the largest expression spec sets on the resolved keyword | −0.4% / −1.2% |
| `916c0b86b` Match the remaining spec sets without `TokenSpec` | −2.5% / −2.3% |
| `eb71d5311` Reuse the keyword lookup that lexIdentifier already performed | **−2.0% / −1.2%** |

The lexer already resolved each identifier's keyword in `lexIdentifier` and
then threw the answer away; the parser re-derived it from the token text on
every `TokenSpec` comparison. Keeping it on the lexeme cost **one byte of
existing padding**. `PrepareForKeywordMatch` had been amortizing the lookup
within a single `switch` but could do nothing across the `at` / `consume(if:)` /
`eat` calls that dominate.

`eb71d5311` finishes that off, and is the tidiest commit on the branch: the
first version cached the keyword on the lexeme but still resolved it in
`nextToken`, so the text was looked up twice for every identifier — once by
`lexIdentifier` to decide whether it had produced a keyword or an identifier,
and again to fill the lexeme in. Threading the first answer through means
`nextToken` need not switch on the token kind at all, because every other path
producing an `.identifier` leaves the field nil, which is what the second lookup
returned for them anyway: their text starts with a backtick, `$`, `<#`, a curly
quote, or a character that cannot start an identifier.

The cost falls mostly on plain identifiers, where the lookup *fails* — a failed
lookup still pays for the length switch and its comparisons, and identifiers are
the most common token kind.

### Character scanning

| | |
|---|---|
| `817307a17` Take an ASCII fast path when advancing over a scalar | **−12.1% / −10.8%** |
| `79bc75d3d` Classify identifier continuation bytes inline | −1.9% / −1.0% |
| `4b95810fa` Decide what trivia is before consuming it | **−9.8% / −11.4%** |

`advance(if:)` copied the whole cursor and decoded a validated UTF-8 scalar
through two closures for every character it merely *looked at*. A byte below
0x80 is a scalar on its own, so ASCII needs neither.

`lexTrivia` consumed a character, decided what it was, and rewound if it turned
out to start a token — paying a 48-byte save per trivia character for a rewind
that happens once per call. It now peeks first.

#### Bytes belong to the position, not the cursor

A reviewer of the ASCII fast path asked whether the scalar read could move to
`Lexer.Cursor.Position`, so that a caller reading a scalar without committing to
it copies a position rather than a whole cursor. It can: `Position` already has
`advance()` — the cursor's forwards to it — so the move needs only a
`Position.peek(at:)`, after which the cursor's version is a one-line forward and
its callers are untouched. Worth about 1% on source that contains multi-byte
scalars, and nothing on source that does not.

That question turned out to reach further than the one call site, and the rest of
this section is what came of it.

| | |
|---|---|
| `dfd8fc3e7` Read a UTF-8 scalar from a position rather than a whole cursor | ~1% on non-ASCII source |
| `a64eedc09` Inline the scalar read rather than special-casing ASCII | −1.1% / −0.3% / −3.4% |
| `b2ec11378` Drop the end-of-file check that `advance(if:)` does not need | neutral |
| `f97d79e48` Scan bytes on Position rather than on Cursor | neutral |
| `b193016db` Remember positions, not cursors, where only bytes are read | neutral to −1% |

Three inputs from here on: the two ASCII ones and
`nonascii_heavy.swift.input`.

**The ASCII fast path was compensating for a missed inlining decision.**
`Unicode.Scalar.lexing` opens with the same `curByte < 0x80` test the fast path
performs by hand, so the special case was never saving the decode. What it was
working around is that `Position.advanceValidatingUTF8Character` was not inlined:
out of line, the position is passed by address, so reading one byte is a pair of
loads and three stores rather than register arithmetic. Marking that method
`@inline(__always)` and deleting the fast path is faster than the fast path was —
1.1%, 0.3% and 3.4% on the three inputs — and twelve lines shorter.

**`lexing` has to stay inlinable as a whole.** Outlining its multi-byte half so
that only the single-byte case is inlined sounds strictly better and measures 5%
slower on non-ASCII source and about 1% slower on ASCII source. The
disassembly says why: with a call in it, the caller stops being a leaf function
and sets up a frame on *every* character, ASCII included. 22 instructions with
the split against 69 without it, and the 69 contain no `bl` and no `stp x29`.

**This does not mean the fast path was a mistake.** On `main` it is worth 12%,
and neither alternative comes close there: the attribute alone measures *+2%*
because `advance(if:)` still copies an 88-byte cursor and now inlines that copy
too, and the full position-based version gets 7%. The fast path only became
removable because `4b95810fa` and `50044b0fe` took the traffic away from it —
`advance(if:)` is called 135,706 and 218,230 times per parse on `main` against
29,939 and 46,609 here, a drop of 78%. A special case earns its keep at one
volume and not at another, and nothing about the code around it says which.

With the scalar read down on `Position`, the rest followed: the `is(offset:at:)`
family and every `advance` function that reads bytes rather than tokens moved
there too, with the cursor keeping one-line forwarders so no call site changed,
and twenty snapshots that existed to anchor a diagnostic or hold a rewind point
became positions instead of whole cursors. A cursor carries the state stack and
the previous token's kind; a position is 24 bytes of pointer, count and
look-behind byte. Keeping the two apart is what stops a byte-level function from
copying token-level state, which is the mistake `advance(if:)` was making.

Twenty-five snapshots still copy a cursor, and four cursor-level APIs are what
hold them there: `starts(with:)`, the `peekBack`/`isLeftBound`/`isRightBound`
trio, and the `slashPosition` and `start` parameters of
`advanceToEndOfSlashStarComment` and `tryLexConflictMarker`. Moving those was
judged not to be worth it: four of the twenty-five are `nextToken`'s, which the
instruction counts show are already elided, and the rest are per-literal or
per-error rather than per-byte.

Nothing became dead API. Renaming every cursor-level member that now forwards to
a position, and building, reports all of them still in use — 94 call sites for
the `is` family, 76 for `peek`, 208 across the `advance` overloads, 12 for
`text(upTo:)`, 8 each for `advanceValidatingUTF8Character` and
`advanceToEndOfLine`, and 28 for the `LexingDiagnostic` initializer that takes a
whole cursor. The split is about which type the work is *written against*, not
about removing entry points: token-level code still asks a cursor for a byte, and
the cursor still asks its position.

### Arena and allocation

| | |
|---|---|
| `5806dcec2` Make the allocator and the parsing arena `final` | ~~−6.1% / −6.3%~~ **wrong; neutral** |
| `d4f3d94e4` Reserve room for the incremental parse lookahead ranges | −2.7% / −2.7% |
| `e8acf42b2` Only record lookahead ranges when someone will read them | −1.7% / −1.9% |
| `aad644153` Refer to the lexer state allocator without owning it | **−4.0% / −3.6%** |

**The 6% attributed to `final` here is wrong.** Re-measured at its own base under
the interleaved two-build protocol, `5806dcec2` is −0.19% / −0.06% — neutral. The
original figure came from the early sequential build-then-measure era that the
methodology notes below warn about, and I never re-measured it when the protocol
changed. Treat every per-commit figure from before the state stack commits as
unverified for the same reason: the ones from `91e26dc86` onward were measured
with two builds interleaved, the earlier ones may not have been.

The reasoning that went with the wrong number — that every allocation was a vtable
call on a non-final `public` class, so the bump could not be inlined — is also
wrong in its second half: `allocate` was not `@inlinable` until `7b2b378a4`, so
devirtualizing it could not have enabled inlining across the module boundary
anyway. `e8acf42b2` changes observable behaviour: `Parser.lookaheadRanges`
is `public internal(set)`, so a caller that drives a `Parser` directly and then
reads it now finds it empty unless it asks for the ranges.

### The state stack (Cursor 48 → 32 bytes)

| | |
|---|---|
| `91e26dc86` Keep the lexer state allocator alive as long as the cursor using it | — |
| `ad179aa76` Hold the lexer state stack as a linked list | **−1.9% / −1.9%** |
| `8886b84d0` Share lexer state stack nodes that stand on the empty stack | +0.6% / +0.3% |

The stack held a pointer to the states below the top, the top state inline, and a
32-bit count: 24 bytes, of which only the pointer is needed if the states are a
list running from the top down. Since a `Cursor` sits in every `Lexeme`, the 16
bytes that frees propagate — `Lexeme` 88 → 72, `LexemeSequence` 160 → 128,
`Lookahead` 272 → 224.

What makes a list workable here is that the nodes are immutable. A cursor is
copied by value into every lexeme, `Lookahead` performs transitions on its own
copy of the sequence, and `advance(by:currentToken:)` restores a cursor saved in
a lexeme — so a stack must not be able to observe another's transitions.
Consing a node satisfies that for free, where the array had to be rebuilt on
every push to get the same property.

Each node carries the number of states below it, because
`hasProgressed(comparedTo:)` compares that and a list cannot count in constant
time. Comparing the top pointers instead is tempting and wrong: a `replace` to a
state equal to the current one allocates a node, so pointer identity would report
progress where the value comparison reports none, and ~80 parser loop guards rest
on that answer. The field is free — it lands in padding the node's pointer
alignment forces anyway.

The third commit pays 0.4% back to fix what the first one costs in memory. With
the top state inline, a stack one deep allocated nothing; as a list, a plain
string literal's push/replace/pop conses ~2.5 nodes, which came to 1,223 nodes on
the declaration-heavy input and 27 KB on a 94 KB string-rich file, none of it
freed until the parse ends. But a node standing on the empty stack is determined
entirely by its state, and those 1,223 nodes are **8 distinct ones** — the 904
string literals in `Cursor.swift` enter 6 distinct states. Looking one up before
allocating takes both inputs to 8 nodes and 192 bytes, restoring the footprint
`LexemeSequence` documents as under 0.1% of the arena.

Only empty-stack nodes are shared, since those are the ones that recur and
matching a whole chain would cost more than it saves; nested interpolation still
allocates, which is why the collections input keeps 66 of its 135 nodes.

`91e26dc86` is a latent bug that this uncovered rather than a change of its own:
`appendUnescapedLiteralValue` passed its state allocator as a temporary of the
`perform` call, so it died at the end of that statement while the cursor lived
on. Nothing read freed memory only because pushing onto an empty stack did not
allocate — which is exactly what the list changes.

### Trivia, a second time

| | |
|---|---|
| `db190d73c` Answer a request for trivia where there is none without scanning | **−5.0% / −3.7%** |
| `cfd6a9383` Take a single space in the trivia fast path | +0.3% / −1.1% |

`lexTrivia` runs twice per token and was the largest single function left. What
the profile did not say is what those calls *do*: instrumenting them showed
**three quarters consume nothing at all** — the byte in front of the cursor
begins a token, and the scan takes one turn of its loop to discover that — and a
further sixth consume a single space.

The bytes the scan stops at turn out to be exactly the printable ASCII
characters other than the three that begin a comment or a conflict marker, which
is four comparisons and no table. Together with taking one space, the fast path
answers **83%** of the calls.

`@inline(__always)` is the whole of it. Left alone the compiler keeps the split
function out of line, which puts a call *in front of* the scan rather than in
place of it, and the profile shows both frames — 3.7% becomes 1%. The same
lesson `7b2b378a4` teaches from the other direction: what matters is not whether
the fast path is small but whether it reaches the caller.

Runs of indentation are a fifth of what still reaches the scan, and taking those
too is tempting, but it needs a loop, and a loop grows the fast path past what
gets inlined. The single space is an `if` for that reason.

Both were verified against the scan directly rather than only through the
corpus: for every byte value, and then for every *pair* of byte values, in each
of the three lexing modes, the fast path agrees on consumed length, newline
presence and error — 196,608 combinations.

### Identifier bytes

| | |
|---|---|
| `50044b0fe` Count an identifier's continuation bytes before moving the cursor | **−1.2% / −2.2%** |
| `e3ff94452` Classify a byte and a scalar from one set of character ranges | neutral |

`advanceOverIdentifierContinuationCharacters` is the widest funnel in the lexer:
**roughly half of every byte in a source file passes through it** — 152,134 of
317,218 across 19,487 calls averaging 7.8 bytes. It took them one at a time, and
each byte cost a bounds check to look at, a second one to consume it, a store of
`previous` and a rebase of the buffer. Counting the run and moving the position
once took 1.75 ns per byte to 1.52.

`Position.advanced(by:)` then became a call per identifier rather than per
incremental reparse, and left out of line it cost 0.019 ms of the 0.036 ms saved,
so it wants `@inline(__always)`. Where a small function lands decides whether
several of the changes on this branch were worth anything at all, in both
directions: see `db190d73c` above and `7b2b378a4` below for it paying, and the
generic `allocate` in *What is left* for it not.

Two things measured *worse* and were dropped. A bit-per-byte-value mask in place
of the ranges: 0.231 ms against 0.229, because the ranges are already four
compares and the mask trades them for a shift, an index and a test. And listing
each of the 64 values in `testCharacterInfo`, which is what it did before
`e3ff94452`: enumerated values lower to a jump table where ranges lower to
compares, worth 0.5% on the collections input.

That last one is why the consolidation is free. The lexer had been spelling out
what `isAsciiIdentifierContinue` accepts, so one classification was written
twice in two files with nothing tying them together; it now lives on `UInt8` in
`CharacterInfo.swift` with the scalar's deferring to it, because a scalar outside
ASCII belongs to none of these sets and one inside it is that byte.

### Crossing the module boundary

| | |
|---|---|
| `7b2b378a4` Inline the bump pointer allocator's fast path into its callers | **−1.7% / −3.8%** |
| `f43212b5b` Combine a token diagnostic only when there is one to combine | −1.5% / −1.5% |

Both come from the same observation: SwiftParser's hot loop calls into
SwiftSyntax, and a call across a module boundary neither inlines nor folds the
constants its caller passes. Bumping a slab is an align, a compare and an add,
and 5.1% of a parse sat in `allocate` and `allocateFromCurrentSlab`.

`@inlinable` on that fast path makes parsing **14% slower**, which is the most
surprising result on the branch. The inlining works — those frames go to zero,
retain traffic and binary size barely move — but inlined into another module the
compiler can no longer prove that the accesses to the allocator's stored
properties do not overlap, so it enforces exclusivity at run time.
`swift_beginAccess` went from nothing to **0.44 ms of the 0.61 ms regression**.
`@exclusivity(unchecked)` on the two properties the bump touches removes them
and the win appears.

That is worth remembering as a shape: an `@inlinable` fast path that mutates
stored properties of a class can pay for itself several times over in dynamic
exclusivity checks, and the checks do not show up as anything recognisable
unless the profile is read symbol by symbol.

The diagnostic commit is the same boundary seen from the other side.
`nextToken` folds a diagnostic into the token three times and for almost every
token all three are `nil`, so it was three calls into another module to be told
the answer is the argument. `@inlinable` on the initializer measures the same as
testing at the call sites, but it is plain public API rather than SPI and has
exactly three callers, so the test went to the callers.

### Reference counting

| | |
|---|---|
| `d3952537f` Hand the lexer its state allocator without retaining it per token | **−1.7% / −1.5%** |
| `9a9c7095c` Work out what a state transition amounts to, then apply it | neutral |

`aad644153`, further up, made `LexemeSequence` hold the allocator
`unowned(unsafe)` so that copying one to start a `Lookahead` neither retains nor
releases, and that was worth 4%. Passing it to `nextToken` gave part of it back,
which took a while to notice:

```
bl <swift_retain>
bl Cursor.nextToken(sourceBufferStart:stateAllocator:)
bl <swift_release>
```

A parameter is guaranteed, which obliges the *caller* to keep the referent alive
for the call, and an `unowned(unsafe)` reference carries no such guarantee — so
the compiler retained and released around every token. `__shared` does not help,
because a non-consuming parameter is already guaranteed; the obligation comes
from where the value came from, not from the convention. Passing it as
`Unmanaged`, which is trivial and promises nothing that has to be kept, removes
the pair, and reference counting over a parse falls from **8.1% to 5.4%**. The
collections work below later took it to 1.7%.

Two things worth keeping from this. `unowned(unsafe)` does not mean "no reference
counting"; it means the *storage* does no counting, and the moment such a
reference meets a call boundary the counting comes back. And the same trap is
still present one level down, at the `Array` the interning cache lives in: a
class property of `Array` type retains its buffer when read and checks uniqueness
when appended to. That one stays, because it happens per state transition — 1,200
times against 86,000 tokens — and does not register in the profile.

`9a9c7095c` is a cleanup that fell out of it, and measures neutral for the same
reason.

### Arena slabs

| | |
|---|---|
| `0c23ecf96` Size a parsing arena's slabs for the source it will hold | **−2.0% / −1.0%** |

A parse allocated in slabs of 4 KB that double only every 128 of them, so filling
the 8.5 MB that parsing the 317 KB input takes asked the system for memory some
500 times, and a quarter of the branch's remaining `malloc` time was
`startNewSlab`.

What made this decidable was measuring the ratio first: a full parse allocates
**roughly 26 times the source** in nodes, text and trivia, and it is remarkably
stable — between 19 and 28 times across six files from 3.6 KB to 317 KB. So the
source size is a good estimate of what to ask for, and a slab that size brings a
parse down to about twenty allocations.

The size goes to the arena's initializer rather than being discovered later,
because only the caller knows whether the arena is about to hold a full parse. An
incremental reparse allocates for what it re-lexes, which the source size says
nothing about, so it passes nothing and keeps the default.

Slabs stay powers of two, doubled up from the default rather than computed. A slab
at twice the source was tried first and rejected: it saves no measurable time and
doubles what is wasted, from 4.7% of the memory a parse takes to 10.8%.

### Collections without an Array

| | |
|---|---|
| `d7ca43ec1` Gather a labeled expression list without an Array | **−2.1% / −2.4%** |
| `4d63b3595` Build every syntax collection without an Array | **−10.2% / −8.7%** |

The largest single change on the branch, and the one that took the longest to
see, because the cost was not in the collection's initializer but in what the
parser handed it. Every collection was built from an `Array`, which the
initializer copied into the arena and then let go.

Counting only the collections that hold anything, over 400 of the parser's own
sources, **60% hold a single element and 94% hold three or fewer**. So each was a
heap allocation, a reference count and a free to carry one or two pointers, and a
parse of the declaration-heavy input built **8,388** of them. It was also
concentrated: `labeledExprList` alone is a third.

CodeGeneration emits one initializer per collection, taking a
`RawSyntaxNodeList`, and the `Array` one is *gone* rather than joined, so nothing
can quietly go back to allocating. Nothing outside SwiftParser was using it — 84
call sites in the parser and three in tests.

The parser gathers into a `RawSyntaxNodeListBuilder` at 53 sites, in memory a
`RawSyntaxNodeListAllocator` owns for the length of the parse. Deliberately not
the syntax arena, whose memory lives as long as the tree: what is gathered is
read once, when the collection is built, so putting it there would leave a buffer
per collection alive for as long as anything holds the tree.

Twenty-five sites still start from an `Array` — a literal handful of elements, or
nodes gathered while recovering from a parse error. Two spellings serve them and
both name the array at the call site, so a hot one cannot hide:
`withRawSyntaxNodeList` borrows the array's storage for the length of the call,
and `RawSyntaxNodeListAllocator.list(_:)` copies where the list must outlive the
expression.

Three things worth keeping.

**Both types have to be trivially copyable**, which is why the builder takes the
allocator as an argument to `append` rather than holding it: one stored class
reference makes every copy of the builder retain and every destroy release. A
small vector holding an `Array` for its overflow case has the same problem — it is
`POD false` even for the 60% of collections holding one element — where overflow
into memory the parser already owns is `POD true` at the same size.

**`initializeElement(at:to:)` does not come down to a store** for a generic
element. Writing through the buffer's base address instead was worth 0.5% of a
parse, which is the difference between this landing at 1.6% and at 2.1%.

**What it did to the profile** is the striking part. Reference counting over a
parse went from 8.1% to **1.7%**, and `malloc`/`free` from 4.3% to **0.6%**. The
arena was always meant to keep a parse away from the allocator; the arrays were
what kept taking it back there.

### Making the tree smaller

| | |
|---|---|
| `77a7fc600` Hold a materialized token's fields behind a pointer | 64 → 56 bytes a node |
| `ffa99ce81` Size a raw syntax node's fields for a file rather than an address space | 56 → **40** |
| `43ad5af60` Sum a layout's byte length and node count without converting | recovers 1.4% of parse time |

The only work here aimed at memory rather than speed, and it started from a
complaint that 26 times the size of the source is a lot to hold a file in.
Measuring where it goes says that it is nearly all one thing:

| | 317 KB input | share |
|---|---|---|
| `RawSyntaxData`, 90,245 nodes | 5.78 MB | **67.8%** |
| layout buffers | 2.42 MB | 28.5% |
| token text | 0.32 MB | 3.7% |
| trivia pieces | 0 | 0% — parsed lazily |

So a node's size is the whole question, and it was 64 bytes. `RawSyntaxData` is a
payload plus an arena reference, and the payload is an enum of three cases, so
every node paid for the largest:

| | before | after |
|---|---|---|
| `.parsedToken` | 44 | 32 |
| `.layout` | 41 | 28 |
| `.materializedToken` | **52** | 8, held behind a pointer |
| `Payload` | 52/56 | **32** |
| `RawSyntaxData` | 64 | **40** |

Three changes, each worth about a third of it.

**The largest case is the one a parse barely makes.** A parse produces
`parsedToken`, which defers trivia; it materializes only what it synthesizes — 6
tokens in the declaration-heavy input and none at all in the collections one. So
`materializedToken`'s fields went behind an `ArenaAllocatedPointer`, which costs
an indirection on error recovery and on programmatically built trees, and nothing
on a parse.

**Four fields were sized for an address space rather than a file.** A parsed
token's `textRange` was two `Int` offsets into a single token's text; a layout's
byte length and descendant count were `Int`s measuring one file. None needs more
than 32 bits.

**Field order was worth as much as the narrowing.** Both `wholeText` and `layout`
are 16 bytes wide and sat behind a one-byte kind, which Swift pads by seven
because it lays a struct out in declaration order. Narrowing alone got the
payload to 37; reordering took it to exactly 32. That is the same finding as
`0c3ccd94b` at the top of this branch, on the other side of the library.

Two things worth knowing before repeating any of it.

**Shrinking one case buys nothing.** `textRange` alone would have left `layout` at
41 setting the payload size, and the node would have stayed 56. An enum is as
large as its largest case, so this only pays when every case moves. That is why
`RawSyntaxData.Payload` is now tracked in the memory layout test: it is the number
that governs.

**Narrowing a field and then adding it up in `Int` gives the space back in time.**
`makeLayout` sums both counters over every child of every node it builds — 302,982
child slots per parse — and reading them through their `Int` accessors converted
on each end of every add. That was **1.4% of a parse**, nearly all of the 2% the
narrowing appeared to cost. Summing narrow leaves 0.5%.

Finding that took three attempts, and the two wrong answers are as instructive as
the right one. It was not the boxing's indirection: the input that slowed most
creates no materialized tokens. It was not the node ceasing to be 64 bytes:
padding it back to 64 measured *worse*. What hid it was diffing profiles **by
symbol**, because the narrowing moved `makeLayout` in and out of its callers, and
a 0.19 ms frame appearing from nowhere looks like a cause. `@inline(__always)` on
it changed nothing, which should have been the clue. Diffing **by cluster** found
it at once: node building accounted for 0.057 ms of a 0.058 ms regression, with
everything else flat and allocation slightly improved.

What remains of the 0.5% is the one conversion still in that loop: a parsed
token's length comes from `wholeText.count`, an `Int` because `SyntaxText` stores
an `Int` count. Narrowing that would remove it and would shrink `SyntaxText`
everywhere else it appears, but it is public API. It would *not* shrink the node
further: `parsedToken` would come to 26 bytes, which alignment rounds back to 32.
A 24-byte payload needs every case within 23, and that one cannot get there
without packing the token diagnostic into spare bits.

#### Tail allocation, which settles the question differently

The paragraph above was right that a payload enum cannot shrink past its largest
case, and wrong that this was the end of it: the enum only has to exist if every
node stores the same shape. `64487d0b4` makes a node a one-word header —
which of four shapes it has, and the arena that owns it — followed by that
shape's fields and then whatever is variable about it.

| | |
|---|---|
| `RawSyntaxData` (the header) | 8 bytes, tag in the reference's spare bits |
| `.smolParsedToken` fields | **4** |
| `.layout` fields | 15/16 |
| `.parsedToken` fields | 20 |
| `.materializedToken` fields | 52/56, inline again |

A layout node is now 24 bytes plus its children *in place*, where it was 40 plus a
separately allocated `8n` buffer, so `makeLayout` writes the children where they
will live and 49,406 allocations per parse of the 317 KB input disappear. A
materialized token stops being boxed, because a node is sized for its own shape
rather than the largest. A parsed token's text is copied into the node, so
`internSourceBuffer` and the arena's copy of the whole source go away — reverting
`1f6c6234f` without reintroducing what it fixed, since the per-token copy is now
part of an allocation the node was making anyway.

**Most tokens do not need twenty bytes of fields.** 99% of them — over the corpus
and both inputs — are present, carry no diagnostic and are shorter than 256
bytes, so presence and the absent diagnostic can be implied by the shape and the
three lengths fit in a byte apiece. That is `.smolParsedToken`, four bytes.

| | consumed, 317 KB input |
|---|---|
| before | 20.90× source |
| header and children in the tail | 18.41× |
| token text in the tail as well | 15.97× |
| four-byte units for short text | **15.36×** |

Two measurement notes, one of which corrects everything above it in this section.

**`totalByteSizeAllocated` is not the footprint.** It sums *requested* bytes and
ignores the padding the bump allocator inserts to align the next allocation.
Every figure in this section before this paragraph is that number; the real
consumption is about 0.9× of source higher before this change and 1.3× after,
because a token node is 12 or 28 bytes plus its text and almost never a multiple
of eight. The table above is consumption, measured by accumulating what each
allocation actually advances the bump pointer by.

**Copying a token's text a word at a time is worth three points of parse time**
over `memcpy`, which spends longer choosing how to copy eight bytes than it does
copying them: a short token becomes one unaligned load and one store. It reads up
to seven bytes past the token, so it is only done where those bytes are inside the
buffer being lexed — hence `setSourceBuffer`. Every safe variant that handles the
tail exactly measured no better than `memcpy`; the speed is in *not* branching.
Short texts move in four-byte units, which costs about a point of time and returns
0.6× of source.

### Cleanups and tests

| | |
|---|---|
| `fc282de88` Describe what `PrepareForKeywordMatch` actually caches | (superseded) |
| `ab06261c3` Drop the unused cursor parameter from the trivia lexing modes | neutral |
| `e93ebdd4c` Track the memory layout of the lexer and parser types | — |
| `c331d96de` Keep the lexer's allocator out of SwiftParser's SPI surface | neutral |

### Removing the assign-and-return pairs

| | |
|---|---|
| `7524ff0b4` Match a lexeme with two local functions rather than two switches | neutral |
| `3077fc191` Drop the last assign-and-return pairs outside the generated sets | neutral |
| `2ac6a490b` Generate the spec set initializers with two local functions | neutral |

A spec set with both token and keyword choices switched twice, and every case of
the first switch had to assign `self` and then `return` so the second switch did
not also run. That is not a shape a compiler checks: omitting one silently
discards the match, which is how `let x = 1` briefly stopped parsing while this
was being written.

Each half is now a local function returning the case it matched, chosen between
with `??`:

```swift
init?(lexeme: Lexer.Lexeme, languageFeatures: Parser.LanguageFeatures) {
  func token() -> Self? {
    return switch lexeme.rawTokenKind {
    case .identifier: .identifier
    default: nil
    }
  }

  func keyword() -> Self? {
    guard let keyword = lexeme.keyword else { return nil }
    return switch keyword {
    case .self: .self
    default: nil
    }
  }

  guard let match = token() ?? keyword() else { return nil }
  self = match
}
```

Beyond removing those pairs from all 117 spec sets — 62 generated and 55
written by hand — this makes the precedence
between the halves one readable line rather than something implied by which
switch was written first — the thing that had `@available(*, deprecated,
message:)` silently swallowed — and puts the keyword unwrap inside the keyword
half, so nothing switches over a `Keyword?`.

Local functions rather than static ones because the calls then need no
qualification: `PrimaryExpressionStart` has a `Self` case, which shadows `Self`
as a type. `OperatorLike` is not a token and keyword split but a chain of three
other spec sets, so it took an `if` / `else if` chain instead.

---

## Correctness

No commit changes the parsed output. The main instrument was a differential
harness: parse every Swift file in the repository with and without the change
and compare a fingerprint of the tree including trivia, the error status, and
round-trip fidelity. **Identical for every commit** — 1,400+ files under the
list the harness used for the earliest commits, 2,987 from the state stack
commits onward.

The corpus contains the files being edited, so a dump taken before an edit and
compared after it reports the edited file as a difference. That caught me four
times, and the fix is to take both dumps as a pair each time rather than reuse an
earlier one. It is worth knowing what it looks like: exactly the files you touched
differ, which reads alarmingly like a real regression.

Where the file-based corpus could not reach, targeted raw-byte corpora were
added:

- **46 trivia cases** — CRLF, bare CR, vertical tab, form feed, byte order
  marks at and after the start of file, truncated marks, unterminated and
  nested block comments, conflict markers, whitespace inside multi-line string
  literals and escaped newlines within them, curly quotes, combining marks that
  cannot start an identifier, whitespace-only and empty files.
- **26 UTF-8 cases** — CJK, emoji, combining marks and non-breaking spaces in
  identifiers, strings, comments and trivia, plus ten malformed sequences: lone
  continuation bytes, truncation mid-file and at EOF, invalid start bytes, bad
  continuation bytes, NUL.
- **Declaration corpus** — every modifier and declaration keyword, those same
  words used as plain identifiers, macro expansion declarations, and modifier
  error recovery.
- **Keyword corpus** — escaped identifiers, contextual keywords in both roles,
  near-miss spellings, keywords in interpolation and regex.

`aad644153` introduces `unowned(unsafe)`, where a lifetime mistake is memory
corruption rather than a wrong parse, so the differential harness is the wrong
instrument. It was verified under **Address Sanitizer**: the whole suite, plus a
stress of the paths that actually spill lexer state — interpolation nested 20
deep, raw string interpolation, regex literals, several hundred sequential
parses to grow the slabs.

Incremental parsing needed its own check for `e8acf42b2`, because a tree
rebuilt without reuse is still *correct*: every incremental test would pass with
node reuse silently dead. Reuse was measured directly instead — an edit inside
one of five top-level declarations reuses four nodes, before and after.

The state stack commits get one more instrument, because a shared node is only
sound while nothing writes to it and a wrong sharing decision would show up as a
state observed in the wrong place rather than as a crash. The number of nodes
allocated per parse is counted directly and compared against the number of
distinct `(next, state)` pairs, which is what says the sharing is total rather
than lucky: 1,223 allocations, 8 distinct nodes, and 8 allocations once shared.

### Two regression tests

`Tests/SwiftParserTest/MemoryLayoutTest.swift` mirrors
`SwiftSyntaxTest.MemoryLayoutTest`, tracking the sizes above.

It also asserts that `Lexer.LexemeSequence` and `Parser.Lookahead` stay
trivially copyable, which no size can express: a strong and an
`unowned(unsafe)` reference are both 8 bytes. Both tests were validated by
reintroducing the bugs they guard — the triviality assertion fails, naming both
types, while the size assertion still passes.

---

## Measured and rejected

Recorded so they are not re-attempted.

| idea | measured | why not |
|---|---|---|
| **Encode keyword kind into `RawTokenKind`** (from `private/perf`) | — | Superseded. `Lexeme` would not shrink — the keyword byte sits in existing padding. Worse, 127 of 180 keywords are contextual and lex as identifiers, so the design resolves them by comparing token text against `defaultText`: a **string** compare where the cached keyword is an integer compare. Benchmarked at **19.8× slower** on a realistic modifier mix. |
| **Skip the lookahead tracker when nobody reads it** | **+5.3% / +5.0%** | See below. The work it would skip is only worth 0.9% / 0.5%, and a null test in `advance()` / `peek()` costs ten times that. |
| Lookup table for `lexNormal`'s dispatch | — | Already a jump table. The disassembly bounds-checks the byte, indexes a table and does an indirect branch; there is nothing to replace. |
| Shrink `Lexer.Result` (104 bytes, larger than `Lexeme`) | ceiling 0.8% | It never escapes, so its sensitivity is 0.01%/byte. Its bulk is `StateTransition?` at 60 bytes, from `pushRegexLexemes` carrying a `RegexLiteralLexemes.Builder` by value; getting it out means threading the state allocator through the regex path for under a percent. |
| Lookup table for `testCharacterInfo` | **0.83×** | The cost was call overhead, not the switch body. Note that `e3ff94452` later found the *form* of that switch does matter: listing each value lowers to a jump table where ranges lower to comparisons, worth 0.5%. So the switch is cheap, but not because the compiler reduces any spelling of it to the same thing. |
| Convert *all* remaining spec sets to switches | **+3%** | Not jump tables, as first claimed — de-hoisting. Fixed by hoisting the field reads by hand, then it was −2.5%. |
| `TokenSpec.Matcher.fixedText` (from `private/parse-attrkeywords`) | **+1.4% / +2.4%** | Grows `TokenSpec` from 5 to 24 bytes; it is built on nearly every parser decision. |
| `final` on `RawSyntaxArena`'s nine members | no gain | `ParsingRawSyntaxArena` being final already lets WMO devirtualize. |
| Drop `Position.previous` | 0 bytes | The flag bytes already occupy that padding. |
| Move `Cursor` out of `Lexeme` | — | Read per token by `hasProgressed` and `currentState`; out-of-lining trades a copy for a bump allocation per token. |
| Take `nextToken`'s positional snapshots as pointers | 415 → 414 instructions | Semantically right — `leadingTriviaStart`, `textStart` and `trailingTriviaStart` are read only for `input.baseAddress` — but the optimizer already elides all three. The hand-written version emits one instruction fewer, one memory op more, and a stack frame 16 bytes larger. |
| Shrink `LexemeSequence` further | ~0.5–1.1% | Only 24 of its 128 bytes are shared/constant; the rest is genuinely per-lookahead. Removing them means dropping the `Sequence` conformance, since `next()` takes no arguments. |

### The lookahead tracker, in detail

Worth recording in full, because the reasoning was sound and the result was the
opposite of what it predicted.

`LexemeSequence` updates a `LookaheadTracker` on every `advance()` and every
`peek()`, and `furthestOffset` has exactly one reader — which is already behind
`collectsLookaheadRanges`, false for a plain parse. So the update is dead work
for every non-incremental parse, and making the tracker pointer optional would
turn it into a null test without growing the struct.

Four builds, each rebuilt from scratch, minimum of 12 interleaved rounds:

| variant | 177 KB | 317 KB |
|---|---|---|
| unconditional update (as shipped) | — | — |
| the update deleted outright, nothing in its place | −0.90% | −0.46% |
| optional tracker, `nil` — the proposed change | **+5.30%** | **+5.02%** |
| optional tracker, non-`nil`, doing identical work | **+10.59%** | **+9.59%** |

The last row is the one that explains it: with the same work performed, merely
routing it through a null test costs 10%. `advance()` is inlined at hundreds of
parser call sites and its `defer` contains the whole lexer by way of
`cursor.nextToken`; the extra basic block is enough to change what the inliner
does with it. Skipping the work recovers only half of what the branch costs.

And the work is worth far less than the first measurement suggested. A single
build with the body spiked out read −2.2% / −1.4%; rebuilt and re-measured
properly it is −0.9% / −0.5%.

Note that `e8acf42b2` gates the *other* half of the same feature — the hash
insertion per registered node — on the same flag, and that was worth 1.7%. The
difference is frequency: a check that runs once per node sits in cold code, while
one per token and per peek lands in the middle of the lexer.

So a plain parse does pay for a tracker nobody reads, and the only way to stop
paying is to get the decision out of the per-token path rather than branch on it
— either a compile-time parameter, which `collectsLookaheadRanges` is not, or
recording once per `Lookahead` instead of once per token. Both are structural
changes worth under a percent, and the second changes when the maximum is taken,
which incremental reuse depends on and a green test suite does not check.

---

## Methodology notes

Four things shaped the process — three mistakes and one technique — all worth
carrying forward.

**Sequential build-then-measure drifts.** Early per-commit figures were wrong —
one commit measured *slower* than its parent on re-test. Everything here is
interleaved A/B with minimums, all binaries built before any timing.

**Build layout adds ~2% of noise.** Deleting an unused type once measured
+2.5%/+4.1%; a clean rebuild of identical source measured +0.3%/−0.2%. Any
result under ~2% from a code-size-changing edit needs a clean rebuild before
it is believed. This was caught only because a botched script accidentally
produced a control build.

The reliable form of that check is to rebuild the *same* source twice and
measure both. Two builds of one tree are not byte-identical — parallel
compilation orders the binary differently — so agreement between them separates
a real effect from layout luck. The lookahead tracker was settled this way: two
independent builds put it at +4.5% and +6.4%, which is how a result that looked
like noise was established as real.

**When the question is whether a copy exists, count instructions, not
nanoseconds.** For an edit meant to remove work rather than change what the
program does, disassembling the one function and comparing instruction count,
memory operations and frame size answers it outright, with none of the layout
noise above and no benchmark input to argue about. That is what established that
`nextToken`'s snapshots are already elided, after a timing run had put the same
question at +0.2% — a number too small to conclude anything from.

**Where a function is inlined decides more than what it contains.** Two of the
larger findings here were inlining decisions rather than algorithmic ones: a
hand-written fast path that existed only because the function under it was not
inlined, and a plausible-looking split of that function that cost 5% because it
stopped its caller from being a leaf. `nm` on the built archive answers the
first question — if the symbol is there with callers, it was not inlined — and
`objdump --disassemble-symbols` answers the second: look for `stp x29, x30`,
which a leaf function does not need.

**A flat measurement on an input that never runs the code says nothing.** The
scalar-read move above first measured neutral, and that was read as evidence that
the copy had been free all along. Counters said otherwise: over the two
performance inputs, `advance(if:)` is called 135,706 and 218,230 times and takes
its cursor-copying path **zero** times, and `peekScalar` is never called at all.
Both inputs are pure ASCII, and the ASCII fast path exists precisely to avoid
that code. The result was not weak evidence of no effect; it was no evidence.
Re-measured on a 321 KB input that is 60% non-ASCII bytes — which runs the path
40,600 times — the change is worth about 1%. Before concluding that a change does
nothing, count how often the code it changes executes.

**A right measurement with a wrong explanation is worse than no measurement**,
because the explanation guides the next decision. The 3% spec-set regression was
attributed to jump-table size; the real cause was de-hoisting field reads. That
wrong reason was recorded in a commit message and blocked the follow-up until it
was corrected — the message has since been rewritten.

Two further notes. Test-suite passes are not always evidence: both the
incremental-reuse and trivially-copyable properties survive a full green suite
while being broken. And a regression test is not finished until it has been
seen to fail — both new assertions were validated that way.

One more, about tooling rather than measurement: a scripted edit that replaced
every occurrence of its pattern, re-run on a file it had already changed, grew
`RawSyntaxArena.swift` to 453,608 lines and left a build spinning on it. What let
it get that far was that the build check reported success from a stale binary.
Scripted edits want asserting on a single match and replacing once.

The measurement set now carries a third input for this reason:
`nonascii_heavy.swift.input`, 321 KB of Swift whose identifiers, string literals
and doc comments are largely CJK, emoji and combining marks. It parses without
errors and round-trips, so it measures the multi-byte scalar paths rather than
error recovery. None of the figures in this report change because of it — every
one of them is a proportion of work the ASCII inputs do perform — but it is the
input that would have caught the mistake above.

One trap appeared three times, on both sides of the colon. In a `switch` over
`Keyword?`, `case .none` matches nil and `case .some` matches every keyword, so
`default` becomes unreachable. In a `switch` used as the expression of a `Self?`
return, yielding a bare `.none` produces nil rather than the case spelled `none`.
Either one silently breaks `precedencegroup`'s `associativity: none`; the first
was caught by a compiler warning, the second by another. Anything named after an
`Optional` case wants naming its type.

---

## What is left

Re-profiled at the branch head, leaf samples over a parse of the 468 KB
declaration-heavy input, 4.64 ms:

| | |
|---|---|
| lexing bytes | **31.3%** |
| parser control flow | 18.0% |
| string literal lexing | 11.3% |
| building nodes | 10.7% |
| arena and allocation | 8.0% |
| keyword and text matching | 7.2% |
| unattributed, mostly `<deduplicated_symbol>` | 6.7% |
| reference counting | 5.5% |
| copying bytes | 1.0% |
| syntax tree wrapper | 0.4% |

and the heaviest single functions:

| | |
|---|---|
| `lexNormal` | 10.3% |
| `nextToken` | 8.7% |
| `lexCharacterInStringLiteral` | 6.7% |
| `RawSyntax.parsedToken` | 4.4% |
| `lexInStringLiteral` | 4.1% |
| `RawSyntaxArena.allocateNode` | 3.2% |
| `lexTriviaByScanning` | 2.9% |
| `LexemeSequence.next` | 2.8% |

A tree is 15.3 times the size of its source, from 26.5 — see *Making the tree
smaller*. What is left there is no longer dominated by one number: a node is a
word of header plus its own shape, so the question moved from "how small can a
payload enum be" to "which of these four shapes can lose a field". The compact
token shape, four bytes for 99% of tokens, is already near the floor, and the
padding the allocator inserts to align the next node is now a comparable cost at
1.3× of the source.

**It is a lexer now, and more so than before.** Lexing plus string literal lexing
is 42.6% of the parse, and each of those functions has already had a pass.
`memset` has disappeared from the profile entirely — it was zeroing layout
buffers, which no longer exist as separate allocations — and `malloc`/`free` is
inside the 8% that all arena work now costs together.

The remaining items, in the order I would look at them, and mostly this argues for
stopping:

- **Parser control flow at 18%.** This is the one cluster that has never had a
  pass: `consumeAnyToken`, the `at`/`eat`/`expect` family and lookahead. It is
  second only to lexing now, and unlike lexing it is not obviously near its floor.
  Whether it holds anything is unknown, which makes it the first thing to measure
  rather than the first thing to change.
- **String literal lexing at 11.3%.** `lexCharacterInStringLiteral` alone is 6.7%,
  the third heaviest function in the parse, and it is the one lexer path that was
  never rewritten — it still consults the state stack per character and copies a
  cursor to look ahead. The declaration-heavy input is full of string literals in
  doc comments and attributes, so this share is real rather than an artifact.
- **Building nodes at 10.7%, of which `RawSyntax.parsedToken` is 4.4%.** After tail
  allocation this is the token factory itself: the keyword precondition, the choice
  of shape, and the text copy. The precondition calls `Keyword.init` on every
  keyword token, which the lexer has already resolved once — the same duplication
  that `eb71d5311` removed on the lexer side.
- **`allocateNode` at 3.2%.** The bump itself, which does not come down by making
  one allocation cheaper. Nodes per parse is the lever, and after the collections
  and tail allocation work there is no obvious surplus left.
- **Reference counting at 5.5%**, up from 2.3% as a *share* because the parse got
  faster around it rather than because it grew. Where it comes from is worth a
  look; the arena work removed the per-token traffic, so what remains is likely
  the `[RawTriviaPiece]` arrays that materialized trivia still allocates.

Two findings from this branch are worth carrying into whatever comes next.
`<deduplicated_symbol>` in a profile is not one function: it is the compiler's
merged-function suffix, so identical generated initializers fold together and the
name shown is arbitrary among them — here it is 3.8%, and it is why the
unattributed row exists at all. And where a small function lands decides whether a
change is worth anything, in both directions — `@inline(__always)` was the
difference between 1% and 3.7% for the trivia fast path, its absence hid a 14%
regression behind an `@inlinable` that looked free, and one hand-written fast path
turned out to exist only because the function under it was not being inlined.

### One loose end

`fc282de88` documents a type that the next commit deletes; it exists only
because of a misreading and could be squashed or dropped.

The dangling state allocator in `StringLiteralRepresentedLiteralValue.swift`,
listed here previously, is fixed by `91e26dc86` — the linked list turned it from
latent into live, which is a fair argument for writing down loose ends when you
find them.
