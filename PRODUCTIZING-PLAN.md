# Productizing `perf-parser-2026-woc`

Splitting the branch into reviewable pull requests. Parsing is 2.6 to 3.0 times
faster across three inputs and the tree is 42% smaller; see PERFORMANCE-REPORT.md
for what each change did and why.

Hashes are as of writing and will change when the squashes are built.

Each PR is built on a branch named `perf-parser-NN-<slug>`, cut from `main` with
`--no-track`. The names have to be flat: the remote already carries a branch
called `perf`, so `perf/NN-slug` is rejected as a directory/file conflict.

The differential corpus is `/Users/rintaro/Repositories/swift-syntax-mono/swift-syntax`
(749 files) rather than this working copy, which moves under the comparison every
time a branch is checked out and reported false differences six times.

## Before anything is posted

**Squash.** Five places where the branch's history is exploratory and the
intermediate states should not ship.

- [x] `6e5ee4ee4` + `ad179aa76` + `8886b84d0` + `9a9c7095c` and `aad644153` +
      `c331d96de` + `d3952537f` → **one commit for all seven**, `694044db4`. The
      state stack became a pointer and a count, then a linked list, then an
      interned one, while the same field was held three ways; only the end state is
      worth reviewing, and the two sets interleave so they cannot be two commits.
- [ ] `ffa99ce81` + `43ad5af60` → one commit, if they are ever cut. Withdrawn as
      a PR of their own; see Group 7. The narrowing introduced a 2% regression that
      the next commit fixes, so the first alone is a regression.
- [x] `d64f96239` + `c2a9dffe8` + `916c0b86b` + `7524ff0b4` + `3077fc191`, plus
      P12's `eca3c7bef` + `2ac6a490b` → one commit, `2b3180eb7`. The last two
      reshape what the first three wrote.
- [x] `79bc75d3d` + `50044b0fe` + `e3ff94452` → one commit. The middle one adds a
      `continuesAnIdentifier` to `Cursor.swift` that the last one deletes, moving
      the classification to `CharacterInfo.swift` where it ends up.

**Drop.**

- [x] `fc282de88`. It documents `PrepareForKeywordMatch`, which the next commit
      deletes. It exists only because I misread the code.

**Leave out.** The nine report commits, about 1,150 lines. PERFORMANCE-REPORT.md
is a working document that cites branch-local hashes and my own measurement
mistakes; it is not something the project should carry. Keep it to draw PR
descriptions from.

## Measuring

Every number in this document was taken with both sides built in one session by
one toolchain. Say which, because it matters more than it should: two patch
releases of the same compiler differ by up to 47% on identical source, and one
eight-line change was free under `6.5.0.9.6` and 19% slower under `6.5.0.10.5`
(rdar://186588859, key path folding). The current default is `6.5.0.11.3`, which
is within 0.5% of `6.5.0.10.5` on this branch.

Prefer retired instructions to wall clock for anything under a few percent. A
timing run's floor across builds is about 0.4% and the first run after a build is
5% to 12% high from cold caches, so a 1% change is not resolvable by clock. The
harness is in `../perf-workspace/harness`: `measure-instr.sh` for instructions,
`measure-two-sides.sh` for wall clock, `measure-memory.sh` for arena bytes,
`measure-toolchains.sh` for one source against two compilers. Keep the machine
quiet — a concurrent build in another session invalidates a timing run, and it has
happened.

## Progress

`origin/main` is `018aecfa9`. Read the state from git rather than from this
prose, which has fallen behind twice; the tables below carry `[x]` for built and
this section for what has landed.

**Merged upstream:** P2, P4, P5+P6, P7, P10, P14, P15.

**In flight on `rintaro/swift-syntax`,** and not to be rebased unless they
conflict: P1 (`8b6983df8`) and P11+P12 (`2b3180eb7`). Neither has a measurement
against current `main`, and P11+P12's base predates P5.

**Cut, verified, unpushed:**

| branch | commit | what it is |
|---|---|---|
| `perf-parser-03-diagnostic-combine` | `21e3f862b` | P3, rebased onto current `main` |
| `perf-parser-09-state-allocator` | `694044db4` | P8+P9 as one commit, **−15.20% / −7.78%** |
| `perf-parser-22-accessor-benchmark` | `2ffdbfac8` | P22, the read-path instrument |
| `perf-parser-30-tail-alloc` | `cde9eead0` | the node header and tail allocation |

The integration branch has since grown a sixth cluster that did not come off the
original branch at all — the Cursor/Position split, described below. It is a PR
in its own right and has to follow P14 and P15.

## The pull requests

Sizes are hand-written lines, with generated lines in brackets. Percentages are
each change against its own parent, on the two performance inputs.

### Group 1 — standalone, small, worth landing first

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P1 | Make the allocator and parsing arena `final` — `5806dcec2` | 4 | **neutral** on `main`: +0.6%/+0.1%, and −0.2%/−0.1% at its own base. The report's −6% is wrong. |
| [x] | P2 | ASCII fast path when advancing over a scalar — `817307a17` | 13 | **−11.3% / −10.6%** vs `main` |
| [x] | P3 | Combine a token diagnostic only when there is one — `f43212b5b` | 12 | −0.5% / −0.5% vs `main`, indistinguishable from noise; 1.0% / 1.0% on the full branch |
| [x] | P4 | Size a parsing arena's slabs for the source — `0c23ecf96` | 48 | **−0.5% / −0.4%** vs `main`, against −2.0/−1.0 at its own base. Slab allocations 412→18 and 519→17; waste up to 4.4% |

Reviewable in minutes each. **The "about 20% between them" I first claimed rests
on per-commit figures that predate the interleaved two-build protocol.** Three of
the four did not reproduce: P1 is neutral, and P3 and P4 are half a percent each.
P2 alone carries the group, at −11.3%/−10.6%.

P1 is a correctness/style change rather than a performance one: `BumpPtrAllocator`
and `ParsingRawSyntaxArena` are not meant to be subclassed. Worth posting on that
basis or dropping, but not as a performance PR.

P3 is worth posting for what it is — a saving of a fixed 0.02–0.04 ms, which is
1% of a fast parse and half a percent of `main`'s — with the number stated
against both bases rather than only the flattering one.

P4 likewise. Its mechanism is much larger than its timing: a parse stops asking
the system for memory hundreds of times, 412 slab allocations falling to 18 on the
collections input and 519 to 17 on the declaration-heavy one, and 15,751 to 5,310
across 400 of the parser's own sources. That is worth half a percent of wall clock
and costs up to 4.4% of the memory a parse takes, so post it as an allocation
change with the memory cost stated, not as a performance one. The branch's 4.7%
was re-measured at 4.4% on this base, in the message and in the doc comment.

P4's cherry-pick conflicts on one line, `collectsLookaheadRanges`, which belongs
to P16. Resolve by taking P4's side without it.

### Group 2 — the lexer's cursor (chained: same struct, same test)

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P5+P6 | Track the memory layout, then shrink `Lexer.Cursor` — `e93ebdd4c` in its consolidated form, then a squash of `0c3ccd94b`, `14d54bd0a`, `1a39c55bc` | 150 + 114 | **−11.1%/−11.7%** and **−10.9%/−10.8%** vs `main`, two builds per input |
| [x] | P7 | Keep the state allocator alive across the cursor — `91e26dc86` | 71 | neutral, as expected: the parse benchmark never reaches this code |
| [x] | P8+P9 | State stack as a shared linked list, and the lexer's allocator held without retaining it — squash of `6e5ee4ee4`, `ad179aa76`, `aad644153`, `c331d96de`, `8886b84d0`, `d3952537f`, `9a9c7095c` as `694044db4` | 188 +/59 − over 7 files | **−15.20% / −7.78%** vs `main` |

P5 and P6 went out as one PR of two commits: the tracked numbers land with
`main`'s values, then one squashed commit moves all of them. Two findings from
building it.

Take `MemoryLayout.swift` from the branch tip, not from `e93ebdd4c`. The tip's
form — which `c331d96de`, a P9 commit, left behind — keeps both layout
dictionaries in that one file, so P5 becomes two new files and 150 added lines
that touch neither `Cursor.swift` nor `Parser.swift`. `e93ebdd4c`'s own form
scatters the dictionaries into those two hot files and makes both import the
`Testing` SPI. The consolidated form builds on `main` with none of P9.

`testLookaheadTypesAreTrivial` cannot land as written: on `main`,
`Lexer.LexemeSequence` and `Parser.Lookahead` are *not* trivially copyable, since
P9 is what makes them so. It became `testCopyingLookaheadTypes`, recording all
four values as data the way the sizes are recorded, so P9 flips two `false`s to
`true` and its benefit shows up as a diff.

**P8 and P9 cannot be split, and not in the order this plan assumed.** P8's third
and fourth commits need `Lexer.StateAllocator`, which P9's `c331d96de`
introduces, and `nodesOnEmptyStack`, which P8's own interning commit adds — so
"P8 before P9" holds only for P8's first two commits. `694044db4` applies all
seven in their original order, P9's first two, then P8's interning, then P9's
third, then P8's transition, which is why they go out as one PR. Measured
together at −15.20% and −7.78%, well past the −1.9% recorded here, because P5's
`Cursor` shrink is on `main` now and the linked list compounds with it.

Sizes, from the tracked layout test: `Lexer.Cursor` 57 → 32 bytes, its
`StateStack` 33 → 8, `Lexer.Lexeme` 97 → 72, `Lexer.LexemeSequence` 192 → 128,
`Parser.Lookahead` 320 → 224. All four of the types a lookahead copies are
trivial, which `testCopyingLookaheadTypes` records as data so the flip shows up
as a diff.

P7 before P8 still holds: the linked list turns that latent use-after-free into a
live one. But P6 and P7 conflict with each other, textually and in both
directions — `0c3ccd94b` and `1a39c55bc` each change one line in
`StringLiteralRepresentedLiteralValue.swift`, and P7's added
`withExtendedLifetime` scope re-indents both of those lines. Verified by
cherry-picking P6 onto P7. There is no semantic disagreement; whichever lands
second is a two-line fixup for its author.

P7 also needs a check of its own. The parse benchmark never reaches
`representedLiteralValue`, and neither does the corpus tree comparison, so
timing and the tree fingerprint both say nothing about it. What covers it is a
digest of every literal's represented value: identical across 749 files and
24,328 represented literals.

### Group 3 — keyword identity

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P10 | Cache the resolved keyword on `Lexeme`, reuse `lexIdentifier`'s lookup — `265f0b27e`, `eb71d5311` | 79 | **−6.5% / −6.6%** vs `main`, against **−10.3/−9.8** claimed at its own base |
| [x] | P11+P12 | Match every spec set on the resolved keyword, hand-written and generated, and delete `PrepareForKeywordMatch` — squash of `d64f96239`, `c2a9dffe8`, `916c0b86b`, `7524ff0b4`, `3077fc191`, `eca3c7bef`, `2ac6a490b` as `2b3180eb7` | 1,694 +/1,009 − over 15 files, mostly generated | −9.8/−7.8, −0.4/−1.2, −2.5/−2.3 for the hand-written part, −0.3%/−0.3% for the generated one; **not measured as a unit** |
| [ ] | P13 | Don't declare attribute names as keywords — `41a10b37b` | 250 [108] | neutral |

P11 and P12 are one pattern repeated across 117 spec sets, and they went out as a
single PR on that basis: splitting them would show a reviewer the same rewrite
twice, once by hand and once through
`templates/swiftparser/ParserTokenSpecSetFile.swift`. The template is in the
branch, so the 1,741-line generated diff is derived rather than hand-edited, and
`swift run --package-path CodeGeneration generate-swift-syntax` should leave the
tree clean. Migrating both halves is what allows `PrepareForKeywordMatch` to go:
107 occurrences on `main`, none on the branch. P13 is independent of the rest of
this group.

### Group 4 — character scanning (independent of each other)

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P14 | Trivia: decide before consuming, then the fast path — `4b95810fa`, `ab06261c3`, `db190d73c`, `cfd6a9383` | 133 | **−9.1%/−10.3% and −10.5%/−10.9%** vs `main`, two builds per input |
| [x] | P15 | Identifier scanning and one character classification — `79bc75d3d`, `50044b0fe`, `e3ff94452` | 96 | **−10.3% / −9.3%** vs `main`, against −3.1/−3.2 claimed across its own bases |

P14 cherry-picks onto `main` cleanly. P15 does not: `50044b0fe` expects the
`extension UInt8` block that P14 introduces, and `main` has no
`advanceOverIdentifierContinuationCharacters` at all — `lexIdentifier` inlines
`advance(while:)` there. So P15's end state was built directly on `main` rather
than cherry-picked, and each of its three pieces checked byte-for-byte against
the branch tip.

Both measured far larger against `main` than against their own bases, for the
reason in the notes below: each is a proportion of the scanning work, and the
scanning work is a larger share of a slow parse.

### The Cursor/Position split — a PR of its own, cascaded after P14 and P15

Five commits, all off the back of review of P2 rather than off the original
branch: `dfd8fc3e7` moves the scalar read to `Lexer.Cursor.Position`,
`a64eedc09` deletes P2's ASCII fast path in favour of inlining that read,
`b2ec11378` drops a redundant end-of-file check, `f97d79e48` moves the
byte-scanning functions down to `Position` behind cursor forwarders, and
`b193016db` converts twenty snapshots from cursors to positions. A sixth,
`251657344`, holds a position as a pointer and one metadata word — the count of
bytes left, with the sign bit saying nothing precedes it — which removes the stored
look-behind byte and takes a `Position` from 17/24 bytes to 16. It has to come last
of the six: it rewrites `advance()`, `advanced(by:)` and `distance(to:)`, which
`f97d79e48` has only just moved onto `Position`. Worth **2.6% / 2.0% / 2.9%** on its
own, which is more than the other five together.

**Order matters here and the plan has to say so.** `a64eedc09` deletes the very
change P2 introduces, and that is only correct downstream of P14 and P15:
`advance(if:)` is called 135,706 and 218,230 times per parse on `main` against
29,939 and 46,609 once the trivia fast path and the identifier byte scan divert
the traffic, a drop of 78%. Measured on `main`, P2's fast path is worth 12% and
the inlining alternative only 7%, so P2 must land as it stands and this PR must
come after P14/P15, not instead of P2.

Worth about 1.1% / 0.3% / 3.4% on the three inputs at the end of the branch. No
cursor API became dead, which is checkable by renaming the forwarders and
building.

`970d1a7ac` belongs with this cluster: it applies the same idea — take the run of
bytes that decide nothing — to string literal segments, and is worth 10.7% of a
parse of the repository's generated sources. It depends on nothing else here.

`scratch-main-inline` holds `08c7d9c98`, the same idea applied to `main` alone:
worth 6.5% on non-ASCII source against the fast path's 4.0%, and a candidate for
its own small PR if the non-ASCII case is worth chasing separately.

### Group 5 — needs a decision before posting

| | | contents | lines | measured |
|---|---|---|---|---|
| [ ] | P16 | Only record lookahead ranges when asked — `d4f3d94e4`, `e8acf42b2` | 63 | −2.7/−2.7, −1.7/−1.9 |
| [ ] | P17 | Inline the bump allocator's fast path — `7b2b378a4` | 33 | −1.7% / −3.8% |

### Group 6 — collections without an `Array` (chained)

| | | contents | lines | measured |
|---|---|---|---|---|
| [ ] | P18 | Introduce `RawSyntaxNodeList`/`Builder`, generate the buffer initializer, convert `labeledExprList` — `d7ca43ec1` | 245 [867] | −2.1% / −2.4% |
| [ ] | P19 | Remove the `Array` initializer, migrate the remaining 83 sites — `4d63b3595` | 772 [1,275] *mechanical* | **−10.2% / −8.7%** |

The largest win on the branch. P19 is one transformation repeated; its size is
call sites, not ideas.

### The node's header and its tail — cut, and it goes first

`perf-parser-30-tail-alloc` (`cde9eead0`) makes `RawSyntaxData` the header — an
enum over the arena reference whose cases name the shape — and puts that shape's
fields in the same allocation, immediately past it. 302 insertions over six
files.

| | |
|---|---|
| arena memory | **−8.40%** requested bytes, −7.94% slab capacity |
| tree size | 26.45× the source → **24.23×** |
| instructions | **−1.12% / −1.11%** |
| header | 64 bytes → **8** |
| node | 64 → 56 for a layout node or parsed token, 64 for a materialized one |

It deliberately changes nothing else: the fields keep their types and order, and
a layout node's children and a parsed token's text keep their own allocations.

**This reverses the order this plan used to give.** It said tail allocation had
to follow Group 7 because `77a7fc600` and `ffa99ce81` shrink the payload it
deletes. Group 7 is now folded into the shape PRs instead, for the reason in that
section, so this lands first and the shape changes build on it.

Two findings worth keeping.

**Leave the header an enum.** Hand-rolling the tag into the low three bits of the
arena address — `struct RawSyntaxData` with a `Kind` and a mask, kept at
`scratch-manual-masking` (`34dbbdb58`) — makes `arenaReference` two instructions
instead of four and costs **4% more work overall**. Swift's own spare-bit choice
is not just a free slot for the tag: it places the discriminator so that the
common test is a single bit, `tbnz #63` separating a token from a layout, which a
three-bit low field cannot do. There are 38 `switch header` sites against 4
constructions, so the switches decide it.

**`RawSyntax` owns the allocation, the arena hands out bytes.**
`allocateNode(byteCount:)` on the arena knows nothing about a node's shape;
`RawSyntax.allocate(_:tailByteCount:arena:)` writes the header and returns
`(node, tail)` for the caller to fill. That is the shape the shape PRs need,
which is why it is worth the three explicit initializers rather than one generic
helper.

Needs saying in the PR: it removes `RawSyntaxData.Payload`, the stored form of a
layout node's fields, and `RawSyntax.rawData` from the `@_spi(RawSyntax)`
surface.

### ~~Group 7~~ — withdrawn, folded into the shape PRs

| | | contents | lines | effect |
|---|---|---|---|---|
| ~~P20~~ | | Hold a materialized token's fields behind a pointer — `77a7fc600` | 106 | node 64 → 56 bytes |
| ~~P21~~ | | Narrow the node's fields and reorder them — `ffa99ce81`, `43ad5af60` | ~250 | node → **40**, tree 26.8× → **20.0×**, ~0.5% slower |

**Not landing on their own.** Both are overwritten by the later changes that
alter a payload's shape — the short-token form above all — so landing them first
means shipping code that the next PRs rewrite, and asking a reviewer to read the
same fields twice. Fold the narrowing into whichever shape PR needs it.

Their figures are requested bytes on the lost 317 KB input, so quote them as the
history of the layout rather than as any current size; the header-and-tail PR
above has measured numbers on the corpus. Their commit messages still carry the
layout reasoning the compaction work builds on, and that reasoning is worth
lifting into the PR that lands the shape rather than losing it.

### Group 8 — compacting the tree (chained, requires the header-and-tail PR)

A non-collection layout node interleaves an `unexpected` slot before its first
child, between every pair and after the last, so *n* children take 2*n*+1 slots.
Over the 749 file corpus **not one of 1,132,225 layout nodes had anything in any
of them** — with every 200th byte deleted it is still under 1% — and those slots
were 56.8% of every layout child slot in the tree. A node now keeps room for them
only when it has something to put there.

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P22 | Read a tree through its typed accessors, as a benchmark — `bb3b8391d`, cut as `2ffdbfac8` | 227 | — |
| [ ] | P23 | `.collection` as its own header case; field accessors made exhaustive — `f89090804`, `be5232589` | 78 | neutral |
| [ ] | P24 | Generate whether a kind interleaves its unexpected children — `e7474384d` | 38 [496] | — |
| [ ] | P25 | Keep no room for unexpected children in a node that has none — `716127f54`, `bb1f9a521`, `587968bf9` | 655 [6,562] | **tree −26%**, parse −1.5%/−1.7% |
| [ ] | P26 | Reach a child by where it sits, not by where the tree says — `0f3933e09` | 68 [3,596] | reads −4.1% |
| [ ] | P27 | One flat case, and read its slots without a test — `b9922d00d`, `a05c1a083`, `d5e8375cd` | 210 | reads **−6.5%** |

**P22 first, and not as a courtesy.** Every performance test in the repository
builds trees or walks them generically; none reads one through the generated
accessors, which is what P26 and P27 change. Without it those two measure as
noise. It counts instructions rather than time, so it resolves effects under a
percent — but the first run after a build is 5% to 12% high from cold caches, and
two sessions measuring one commit differ by about 0.4%, which is the floor on any
comparison across builds.

**The whole group sits on the header-and-tail PR**, not on Group 7: compaction
assumes a node's children are tail allocated, which is what `cde9eead0` provides.
P23 and P24 are prerequisites with nothing to show on their own: P23 is the header
case with both shapes still identical, P24 a generated `SyntaxKind` property.

**P25 and its mutation tests cannot be split.** Every mutating operation hands its
layout back to `makeLayout`, which decides the shape afresh — that is what keeps a
rewritten node compact and what let `SyntaxRewriter` go untouched. Landing the
compaction without that would silently re-expand every rewritten tree.

Two things a reviewer will want, and neither is in the diffs. `RawSyntaxData` gains
three shapes where it had one, and the four checked field accessors ended in
`default:` arms that the compiler could not flag — that is why P23 makes them
exhaustive before any shape is added. And nearly all of P26 and P27's gain is *not*
asking `SyntaxKind` a question the header answers: `isSyntaxCollection` and
`interleavesUnexpectedChildren` are switches over three hundred kinds that sat on
per-node paths, which is why merging the flat cases in P27 was worth more than
every other read-path change together.

### Group 9 — lookahead allocations (standalone, independent of everything else)

Attributing every retain, release and allocation to its caller put reference
counting at 13.3% of a parse, of which 9.6% was `Array` machinery — and half of
that was in lookahead. Neither of these is an algorithm change; both are an
allocation that did not need to happen.

| | | contents | lines | measured |
|---|---|---|---|---|
| [ ] | P28 | Push a skipping state without allocating an array to hold it — `a5ac88b83` | 24 | −1.6% / **−3.9%** / −0.7% |
| [ ] | P29 | Ask a spec set for its cases once — `3ce750382`, reverted in `cb62d8055`, re-applied as `a196f3daa` | 14 | **−2.0% / −1.3%** in retired instructions |

Percentages are collections, declaration-heavy and non-ASCII, each against the
commit's own parent. The spreads are opposite and that is the point: skipping
costs the declaration-heavy input most, recovery costs the collections one most.

`Lookahead.skip(initialState:)` pushed onto its state stack with
`stack += [a, b]`, which builds a temporary array for every push, on the path
malformed input and every speculative parse take. `canRecoverTo(anyIn:)` asked
`specSet.allCases` three times — four with alternate token introspection enabled,
which is why the hoist has to go above that `#if` — and each call builds a fresh
`Array`, one of which it then reduced through a second array it discarded.

Two notes for review. **P29 must keep the closure.** The hoist itself is free; the
cost that got it reverted was the same commit rewriting
`.map({ $0.spec.recoveryPrecedence })` as `.lazy.map(\.spec.recoveryPrecedence)`,
which leaves the key path unfolded under `swiftlang-6.5.0.10.5` and costs 32M
instructions a parse. That is rdar://186588859. `a196f3daa` re-applies the hoist
with `.lazy.map({ closure })`, the spelling that is correct under both toolchains
and the fastest of the four. **Recursion is the wrong fix for the first**: `01e94a1af`
deliberately removed it, and the explicit stack is what bounds the depth on
adversarially nested input. And what is left in each is the array itself — an
inline buffer with a count for the skipping stack, as the lexer's state stack
already does, and for the spec set a `static let allCases`, **for the generated
conformances only**. The template emits all 62 of them, so it is one change rather
than 62 judgements, and the payoff sits in their tail: the median is 4 cases but
`NameOptions` has 68, `AccessorSpecifierOptions` 33, `LayoutSpecifierOptions` 18.
The 54 hand-written conformances are the same size as the generated median and
live in parser source people read, so adding a stored global to each buys little
and costs clarity. Unmeasured either way.

### Not yet assigned to a PR

Work that landed after this plan was written and has no row above. None of it is
large; it needs homes rather than analysis.

| | where it belongs |
|---|---|
| `0ae93a368` Derive a lexeme's `start` from the cursor it was lexed from — 72 → 64 bytes, ~2% on every input | its own small PR, or with the Cursor/Position split, since it is the same argument about what a lexeme stores |
| `970d1a7ac` Scan the run of ordinary bytes inside a string literal — −10.7% on the declaration-heavy input | its own PR; independent of everything, and the third instance of the run-scanning shape |
| `e12075211` Stop tracking `Parser`'s size | fold into P5, which is the PR that introduces the tracking; `Parser` gains stored properties under `SWIFTPARSER_ENABLE_ALTERNATE_TOKEN_INTROSPECTION`, so one expected number cannot describe it |
| `c01c36234` List the added sources in the CMake builds | **split across the PRs that add those files** — P5 for `MemoryLayout.swift`, Group 6 for `RawSyntaxNodeList.swift` and `RawSyntaxNodeListBuilder.swift`. A PR that adds a file and not its CMake line breaks the CMake build while SwiftPM stays green |

## Needs your sign-off

- [ ] **P17** rests on `@exclusivity(unchecked)`. Without it the change is a 14%
      regression, so it is the premise, not a detail.
- [ ] **P16** changes observable behaviour: `Parser.lookaheadRanges` is
      `public internal(set)`, and a caller driving `Parser` directly now finds it
      empty unless it asks for the ranges.
- [ ] **P19** removes an initializer from every collection node under
      `@_spi(RawSyntax)`. Nothing outside SwiftParser used it.
- [ ] **P20/P21** change `RawSyntaxData`'s layout and put `MaterializedToken`
      behind an indirection, which is visible through `RawSyntaxTokenView`.

CI has `api_breakage_check_enabled: false`, so none of these trip a check
automatically. They want saying in prose.

## Suggested order

1. **P22 now**, and P3 with it. P22 is a test file that depends on nothing, and
   the read-path changes in Group 8 measure as noise without it. Landing it before
   the changes it measures also keeps it from looking like a benchmark written to
   flatter them.
2. **P8+P9**, which is cut and measured at −15.20% / −7.78%, the largest single
   result left. P7 is already upstream, so nothing blocks it.
3. **The header-and-tail PR**, which is cut. Everything in Group 8 assumes it.
4. Groups 3 and 4 in parallel with the above where they do not collide — P11+P12
   is already in flight, P13 is independent of it.
5. Group 5 once the two questions above are settled.
6. Group 6 last among the parser work: it is the largest, touches CodeGeneration
   and most parser files, and wants a quiet base.
7. Group 8 after the header-and-tail PR, in its own order.
8. Group 9 whenever convenient. Two small diffs in two files, dependent on
   nothing, and between them worth more on the declaration-heavy input than most
   of Group 1.

## What "done" means for each PR

Each should carry its own measurement and its own verification, not the branch's
cumulative numbers.

- [ ] Interleaved A/B against the PR's own base, two independent builds per side,
      minimum of ≥12 rounds. A sub-2% claim from a code-size-changing edit is not
      believable from one build.
- [ ] Differential parse of every Swift file in the repository, comparing a tree
      fingerprint including trivia, the error status, and round-trip fidelity.
      Take both dumps as a pair; a dump taken before an edit reports the edited
      file as a difference, which caught me five times.
- [ ] The raw-byte corpora where the change touches lexing: 46 trivia cases, 26
      UTF-8 cases.
- [ ] Incremental reuse measured directly where the change touches lookahead or
      the arena — a tree rebuilt without reuse is still correct, so the tests pass
      either way.
- [ ] `swift format --in-place --parallel --recursive`, generated sources
      excluded.
- [ ] `swift test` green *and* exit code 0. The layout tests fail the run without
      failing a count.

## Notes carried from the work

- Where a small function lands decides whether a change is worth anything, in
  both directions. `@inline(__always)` was the difference between 1% and 3.7% for
  the trivia fast path; its absence hid a 14% regression behind an `@inlinable`
  that looked free.
- Taking a run of bytes that decide nothing has now paid three times — trivia,
  identifiers, string literals — and each time the per-character path was doing
  work whose result the caller discarded. It is the first thing to look for in a
  scanner.
- A copy costs something when the value is *stored*, and nothing when it is not.
  Eight bytes off `Lexer.Lexeme`, which every token advance and every peek copies
  and which two larger structs embed, is worth 2%. Eight bytes off a rewind that
  the optimizer can see through is worth nothing, four times over.
- A copy that does not escape costs nothing, and this branch has now measured that
  three times: `nextToken`'s 88-byte snapshots, the scalar read's cursor, and the
  string literal rewinds at 32 bytes against 24. Stop proposing it as an
  optimisation; propose it as layering, if at all.
- Measure the footprint, not the request. `totalByteSizeAllocated` sums requested
  bytes and ignores the padding the allocator inserts to align the next
  allocation, which here is 1.3× of the source — about 7% of the tree. Accumulate
  what each allocation advances the bump pointer by instead.
- An enum payload cannot shrink past its largest case, but the enum only has to
  exist if every node stores the same shape. Tail allocation asks the question
  differently and got 27% where narrowing fields got single digits.
- Where a small function is inlined can matter more than what it does. A
  hand-written ASCII fast path turned out to exist only because the function
  under it was not inlined; and splitting that function so only its cheap half
  inlines cost 5%, because the caller stopped being a leaf and set up a frame on
  every character. `nm` answers whether something was inlined; `objdump
  --disassemble-symbols` and a search for `stp x29, x30` answers whether the
  caller is still a leaf.
- A special case earns its keep at one call volume and not another, and the code
  around it does not say which. Measure the volume, not just the time.
- Count how often the changed code runs before believing a flat measurement. The
  scalar-read move measured neutral because both performance inputs are pure
  ASCII and take that path zero times out of 135,706 and 218,230 calls — no
  evidence rather than weak evidence. On a 60% non-ASCII input it is worth 1%.
- Narrowing a field and then adding it up in `Int` gives the space back in time.
- A change worth a *proportion* of some phase measures larger against `main` than
  against a fast base, and a change worth a *fixed quantity* measures smaller.
  P14 and P15 each roughly tripled against `main`; P3 halved and P4 fell to a
  fifth. Neither direction is a measurement error, and the base has to be named
  with the number.
- A mechanism can be much larger than its timing. P4 removes 95% of a parse's slab
  allocations for half a percent of wall clock. Measure the mechanism too, or there
  is nothing to say about a change whose time saving is within noise.
- `<deduplicated_symbol>` in a profile is not one function. Diff profiles by
  cluster, not by symbol: inlining decisions move between builds and symbol-level
  diffs attribute that motion to the wrong place.
