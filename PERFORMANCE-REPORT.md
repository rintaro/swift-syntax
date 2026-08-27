# SwiftParser performance work — 2026-08

Branch `perf-parser-2026-woc`, 41 commits off `main` (`a3cd836bf`).
Commit hashes below are as of writing; rebasing the branch will change them,
so the subject lines are the stable reference.

**Parsing is 2.32× faster on a 177 KB source file and 2.19× on a 317 KB
declaration-heavy one**, with no change to the parsed output.

| input | main | branch | |
|---|---|---|---|
| `MinimalCollections.swift.input` (177 KB) | 4.899 ms | 2.115 ms | **−56.8%** (2.32×) |
| concatenated parser sources (317 KB) | 8.394 ms | 3.825 ms | **−54.4%** (2.19×) |

Repeated runs of this pair vary by a few percent; treat it as roughly 2× and
1.9×.

Interleaved A/B, 16 rounds, minimum per rev, both ends rebuilt from source.

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

Self time normalized to absolute cost per parse (shares alone are misleading
when the total halves).

| cluster | main | now | change |
|---|---|---|---|
| Unicode decode / classify | 0.317 ms | 0.016 ms | **−95%** |
| TokenSpec / spec sets | 0.543 | 0.080 | **−85%** |
| Keyword recognition | 0.555 | 0.123 | **−78%** |
| Struct copy value-witness | 0.259 | 0.063 | **−76%** |
| Trivia lexing | 0.567 | 0.234 | **−59%** |
| Identifier lexing | 0.323 | 0.135 | **−58%** |
| Lexer dispatch | 0.544 | 0.403 | −26% |
| ARC | 0.137 | 0.126 | −8% |
| Arena / allocation | 0.333 | 0.318 | −4% |
| **whole parse** | **4.813** | **2.600** | **−46%** |

Arena allocation looks untouched here because this table predates two of the
three arena commits; its share rose only because everything else shrank. The
table also predates the three state stack commits, which took another 1.4% off
the whole parse.

### Struct sizes

| type | main | now |
|---|---|---|
| `Lexer.Cursor` | 81 / 88 | **32 / 32** |
| `Lexer.Cursor.State` | 17 / 24 | **10 / 16** |
| `Lexer.Cursor.StateStack` | 41 / 48 | **8 / 8** |
| `Lexer.Lexeme` | 121 / 128 | **72 / 72** |
| `Lexer.LexemeSequence` | 320 / 320 | **128 / 128** |
| `Parser` | 456 / 456 | **344 / 344** |
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

### Arena and allocation

| | |
|---|---|
| `5806dcec2` Make the allocator and the parsing arena `final` | **−6.1% / −6.3%** |
| `d4f3d94e4` Reserve room for the incremental parse lookahead ranges | −2.7% / −2.7% |
| `e8acf42b2` Only record lookahead ranges when someone will read them | −1.7% / −1.9% |
| `aad644153` Refer to the lexer state allocator without owning it | **−4.0% / −3.6%** |

Two words of `final` were worth 6%: every allocation was a vtable call on a
non-final `public` class, so the bump — a pointer compare and an add — could not
be inlined. `e8acf42b2` changes observable behaviour: `Parser.lookaheadRanges`
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
lesson as the allocator two sections up, from the other direction: what matters
is not whether the fast path is small but whether it reaches the caller.

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
so it wants `@inline(__always)` — the third time on this branch that where a
small function lands decided whether the change was worth anything.

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
the pair, and reference counting over a parse falls from **8.1% to 5.4%**.

Two things worth keeping from this. `unowned(unsafe)` does not mean "no reference
counting"; it means the *storage* does no counting, and the moment such a
reference meets a call boundary the counting comes back. And the same trap is
still present one level down, at the `Array` the interning cache lives in: a
class property of `Array` type retains its buffer when read and checks uniqueness
when appended to. That one stays, because it happens per state transition — 1,200
times against 86,000 tokens — and does not register in the profile.

`9a9c7095c` is a cleanup that fell out of it, and measures neutral for the same
reason.

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

Beyond removing all 55 pairs across the 62 spec sets, this makes the precedence
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
list the harness used for the earlier commits, 2,987 for the state stack ones.
Files the commit itself edits are compared separately against frozen copies of
their pre-change contents, since otherwise a content change reads as a parser
change; that trap caught me three times.

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
| Lookup table for `testCharacterInfo` | **0.83×** | The compiler already lowers that switch to a bitmask test. The cost was call overhead, not the switch body. |
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

Three mistakes shaped the process, all worth carrying forward.

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

**A right measurement with a wrong explanation is worse than no measurement**,
because the explanation guides the next decision. The 3% spec-set regression was
attributed to jump-table size; the real cause was de-hoisting field reads. That
wrong reason was recorded in a commit message and blocked the follow-up until it
was corrected — the message has since been rewritten.

Two further notes. Test-suite passes are not always evidence: both the
incremental-reuse and trivially-copyable properties survive a full green suite
while being broken. And a regression test is not finished until it has been
seen to fail — both new assertions were validated that way.

One trap appeared three times, on both sides of the colon. In a `switch` over
`Keyword?`, `case .none` matches nil and `case .some` matches every keyword, so
`default` becomes unreachable. In a `switch` used as the expression of a `Self?`
return, yielding a bare `.none` produces nil rather than the case spelled `none`.
Either one silently breaks `precedencegroup`'s `associativity: none`; the first
was caught by a compiler warning, the second by another. Anything named after an
`Optional` case wants naming its type.

---

## What is left

Measured on the declaration-heavy input at the branch head, 3.83 ms:

| | |
|---|---|
| `nextToken` (with the trivia fast path inlined into it) | 8.0% |
| `lexNormal` | 7.4% |
| `lexIdentifier` (with the identifier scan inlined into it) | 6.9% |
| `lexTriviaByScanning` | 5.8% |
| generated `Raw*Syntax` initializers | ~4% |
| reference counting | 5.4% |
| `malloc` / `free` | 4.3% |
| `memset` | 2.0% |

By cluster: lexer scanning 33%, node construction ~13%, arena 8%, reference
counting 5%.

Three things learned while arriving at those numbers, each of which changes what
is worth trying next.

**`<deduplicated_symbol>` was 4% of the profile under a name that says nothing.**
It is the compiler's merged-function suffix `Tm`: the generated `Raw*Syntax`
initializers have identical bodies for a given layout shape and get folded into
one, along with small accessors. So node construction is ~13%, not the ~4% listed
here before, and per-name attribution in that region is unreliable, because the
name shown is arbitrary among the folded set.

**Allocation cannot be made cheaper, only rarer.** `BumpPtrAllocator`'s frames
looked like 5% of call overhead, but forcing the generic `allocate` inline moved
0.203 ms out of it and 0.206 ms into `RawSyntaxArena.intern` and
`allocateRawSyntaxBuffer` — the immediate callers, which then stopped being
inlined themselves. The bump *is* the work: an align, a compare, an add and a
store per node.

**26% of the `malloc` time is `startNewSlab`.** The parsing arena starts at 4 KB
and doubles only every 128 slabs, so filling a few MB takes hundreds of small
mallocs. This is the one cheap experiment left that nobody has run: a larger
initial slab, or a shorter doubling interval. It needs watching memory as well as
time, since the risk is over-allocating for small files.

Beyond that, `lexNormal` at 7.4% is already a jump table with its cost spread
across the case arms, and `nextToken` at 8.0% is the orchestrator with two fast
paths inlined into it. The remaining reference counting is 37% inside those merged
node initializers and would want looking at there rather than in the lexer.

### One loose end

`fc282de88` documents a type that the next commit deletes; it exists only
because of a misreading and could be squashed or dropped.

The dangling state allocator in `StringLiteralRepresentedLiteralValue.swift`,
listed here previously, is fixed by `91e26dc86` — the linked list turned it from
latent into live, which is a fair argument for writing down loose ends when you
find them.
