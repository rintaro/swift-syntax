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
(rdar://186588859, key path folding). The current default is `6.5.0.12.5`. It moves
the headline by less than the noise — the four inputs measure 3.06×, 3.07×, 2.37× and
2.78× against `main` where `6.5.0.12.4` gave 3.02×, 3.01×, 2.42× and 2.76×, with the
instruction ratios equal to two decimal places — and `6.5.0.11.3` before it was within
0.5% of `6.5.0.10.5` on this branch. Whether it still carries rdar://186588859 has not
been checked.

Prefer retired instructions to wall clock for anything under a few percent. A
timing run's floor across builds is about 0.4% and the first run after a build is
5% to 12% high from cold caches, so a 1% change is not resolvable by clock. The
harness is in `../perf-workspace/harness`: `measure-instr.sh` for instructions,
`measure-two-sides.sh` for wall clock, `measure-memory.sh` for arena bytes,
`measure-toolchains.sh` for one source against two compilers. Keep the machine
quiet — a concurrent build in another session invalidates a timing run, and it has
happened.

## Progress

`origin/main` is `e9289aa44`. Read the state from git rather than from this prose,
which has fallen behind twice; the tables below carry `[x]` for built and this
section for what has landed.

**Merged upstream:** P2, P3 (3448), P4, P5+P6, P7, P8+P9 (3425), P10, P11+P12 (3420),
P14, P15, P22 (3437), P28 (3434), P29 (3435), the string literal run scan (3427), the
keyword lookup (3449), the header and tail (3426), and scanning on a position (3454, cut
as `perf-parser-38-position-scanning` from the first five commits of the Cursor/Position
split).

**Open as pull requests,** and not to be rebased unless they conflict:

| | | branch | what it blocks |
|---|---|---|---|
| 3453 | parsed token | `perf-parser-33-parsed-token` | the layout PR, by construction |
| 3455 | position as a pointer and a metadata word | `perf-parser-32-position-compaction` | `perf-parser-39-optional-previous`, which sits on it |
| 3447 | P16 | `perf-parser-16-lookahead-ranges` | nothing |

3453 sits directly on `911061a67`, the merge of 3426, and measures **−1.35%, −1.15%,
−0.81%, −1.01%** in instructions over two pairs, with the arena allocating 21.9% less over
the corpus: a tree goes from 24.25× its source to 18.94×. 3447 was rebased onto
`e9289aa44` as `832894e03` — 3425 touched the same initializer — and is worth more there than it was:
**−3.75%, −3.11%, −3.63%, −0.10%** over two pairs, against −2.86%, −2.51%, −3.02% and
−0.17% on the base before. Nothing about the commit changed; 3425 made the parse faster,
so a fixed cost per node is a larger share of it.

**Landing 3425 clears the queue in `Cursor.swift`.** P3, the Cursor/Position split and
the parsed-token PR were all waiting on it. The split's hold is over; it is next in the
order below.

**What landing 3420 unblocked:** P13, P18 and P19, which share the parser's declaration
and expression files with it. **What landing 3437 settled:** the layout PR's read
figures have their instrument upstream, and it is the corrected one — `c4ea3b82b`, which
recurses through the accessors and iterates each list as a `SyntaxCollection` rather than
walking `children(viewMode:)`. Any branch cut from `main` now carries it, so measuring a
read path no longer needs the benchmark grafted on from elsewhere.

**What landing 3427 unblocked:** P3 and the Cursor/Position split were waiting on it for
`Cursor.swift`, and both now apply cleanly.

**Cut, verified, unpushed.** P3 sits on `1f995c731`, twelve commits back and still
conflict-free; the tail-allocation chain and the split predate `e9289aa44` by 64. What
3425 left behind is a conflict in `Tests/SwiftParserTest/MemoryLayoutTest.swift` for the
split, the parsed-token branch and the layout branch — it changed `Lexer.Cursor`'s size,
so the expected numbers moved — and the layout branch additionally conflicts in generated
files, which regenerating settles.

Every measurement quoted here was taken against the base it was cut from, and rebasing
onto `e9289aa44` means re-measuring: P16 went from −2.86% to −3.75% on one input by
moving base alone, and P3 from −0.5% to −1.4% earlier. Neither commit changed.

| branch | commit | what it is |
|---|---|---|
| `perf-parser-03-diagnostic-combine` | `4c132607d` | P3 on `e9289aa44`, **−1.9% / −2.0% / −1.3% / −3.7%** across the four inputs |
| `perf-parser-36-keyword-lookup` | `616abc45f` | keyword lookup by the packed bytes, **−2.2% / −1.3% / −1.0% / −2.6%** across the four inputs |
| `perf-parser-16-lookahead-ranges` | `832894e03` | P16 on `e9289aa44`, **−3.8% / −3.1% / −3.6% / −0.1%** across the four inputs; posted as 3447, red once, fixed |
| `perf-parser-09-state-allocator` | `694044db4` | P8+P9 as one commit, **−15.20% / −7.78%** |
| `perf-parser-30-tail-alloc` | `ac52caf57` | the node header and tail allocation, then reading that tail through one reference and allocating it through one function per shape |
| `perf-parser-33-parsed-token` | `eeeee643e` | a parsed token's text in its tail, then the four-byte shape for a short one — sits on the branch above |
| `perf-parser-35-compact-layout` | `7aa4d8bfc` | the layout node compacted, **tree 18.91× → 10.14× the source**, parse −3.4% / −3.2%, client reads −0.1% to −1.4% — sits on the branch above |
| `perf-parser-37-nexttoken-locals` | `cb4d06e2f` | `nextToken` tidied: one copy of where a lexeme starts, the previous lexeme's newline held without an `Optional`, and trailing trivia adding a newline rather than replacing one — **−0.35% / −0.35% / −0.23% / −0.49%** across the four inputs |
| `perf-parser-39-optional-previous` | `167d24103` | a position's `previous` is `nil` at the start of the input rather than nul, so a conflict marker straight after a mid-file nul is no longer taken as one; a test covers it. Neutral: one function, `TriviaParser.parseTrivia`, 12 bytes smaller, and instructions within noise. Sits on 3455 |
| `perf-parser-28-lookahead-skip` | `65a29f4d0` | P28, capacity reserved at 8 |
| `perf-parser-29-specset-allcases` | `38ce300d2` | P29, the hoist with its key-path workaround |

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
| [x] | P3 | Combine a token diagnostic only when there is one — `f43212b5b` | 12 | **−1.9% / −2.0% / −1.3% / −3.7%** against `e9289aa44` |
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

**P3 has been re-measured twice as `main` moved, and grows each time.** On the base it
was cut from it read −0.5%, inside the noise. On `1f995c731` it read −1.39%, −1.46%,
−0.97% and −3.27%. On `e9289aa44`, rebased as `4c132607d`, it reads **−1.90%, −2.01%,
−1.31% and −3.71%**, pairs agreeing within 0.1 points. The commit has not changed once:
nine lines in `Cursor.swift`. Each landed PR removes work a parse used to do, so what
this saves is a larger share of what is left, and the same arithmetic took P16 from
−2.86% to −3.75%. The largest win is on the corrupted input, which is where token
diagnostics actually occur, and the smallest on the non-ASCII one.

It is also a clean demonstration of why this plan says to prefer instructions. On the
declaration-heavy input wall clock read +0.64%, +0.83% and then −1.06% across three
independent build pairs — sign unstable, magnitude about a percent either way — while the
instruction count read −1.46%, −1.47% and −1.43%. Quoting the wall clock from either of
the first two pairs would have reported a regression that does not exist.

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

### The Cursor/Position split — cut, and held

`perf-parser-32-position-compaction` (`f568c63ed`) holds all six as one PR, rebased onto
`e9289aa44`. Two conflicts: `Cursor.swift`, where the landed string literal run scan and
this branch's move of the byte-scanning family both add to the same extension and both
belong, and the layout test's numbers. Builds, suite passes, lint clean.

**The hold is over:** it waited on `perf-parser-09-state-allocator`, which landed as
3425. What that leaves is a rebase whose only conflict is the layout test's numbers,
since 3425 changed `Lexer.Cursor`'s size — and a re-measurement, because the size claim
below was about the shape `Cursor` had before it.

**It now blocks one thing:** the first-lexeme flag, `7577f33f0`, seeds
`previousLexemeTrailingNewlinePresence` from `isAtStartOfInput`, which this branch
introduces. That change is to be cut on top of this one rather than rewritten against
main's previous-byte cursor.

**Measured on `e9289aa44`**, two pairs agreeing within 0.04 points: **−0.33%** on
`MinimalCollections`, **−0.48%** on the declaration-heavy input, **−2.26%** on the
non-ASCII one and **−1.54%** on the corrupted one. That is a fraction of what the parts
measured on the branch they came from, and the reason is everything that has landed since:
P14, P15 and the string literal run scan took most of the traffic off the paths this
moves, and the inlining that replaces P2's ASCII fast path is worth less the less that
path runs. What is left is a real win on non-ASCII source and close to noise on ASCII.

**The size claim was expected to change with 3425 and did not.** `Position` goes from
17/24 bytes to 16/16 as before, but `Lexer.Cursor` stays at 32/32 — the prediction was
that repacking `Cursor` would turn those eight bytes into a size win, and measuring it
says they land in padding again, with `Lexeme` at 72, `LexemeSequence` at 128 and
`Lookahead` at 224 all unchanged. The value here is cheaper operations from dropping the
stored look-behind byte. Do not quote it as a memory change.


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
| [x] | P16 | Only record lookahead ranges for a parse that hands them on — `d4f3d94e4`, `e8acf42b2` | 63 | **−2.9%, −2.5%, −3.1%, −0.1%** |

**Cut as `perf-parser-16-lookahead-ranges`, `f7d88c52f`, one commit on `1f995c731`.**
Measured over two independent build pairs, agreeing within 0.05 points: **−2.94%** on
`MinimalCollections`, **−2.47%** on the declaration-heavy input, **−3.03%** on the
non-ASCII one, and **−0.09%** on `corrupt_heavy` — nothing at all on the last, which is
the one input that spends its parse recovering rather than registering reusable nodes.

**3421 changed P16's ground, and the correction is in the gate.** `main` preserves
lookahead ranges across incremental parses and for reused nodes, and `Parser.init` seeds
them from the transition it is given. P16 gates recording on `collectsLookaheadRanges`,
which the `parseIncrementally` entry points set to true and everything else defaults to
false, so the gate now includes the transition: record when asked **or** when parsing
incrementally.

**3447 went red on sourcekit-lsp, and the default was why.** The failure was
`SourceKitLSPTests.LocalSwiftTests.testIncrementalParse`, with
`Expectation '[reused node callback called]' not fulfilled`.
`SyntaxTreeManager` drives a chain of `Parser`s itself — it constructs one, parses, and
builds an `IncrementalParseResult` from `parser.lookaheadRanges` — so its *first* parse
has no transition, recorded nothing under an opt-in default, and handed on an empty
table; after which nothing was ever reusable. The gate covers a parse that is *given* a
transition, not one that will be *handed on*, and nothing in the signature distinguishes
them.

`collectsLookaheadRanges` therefore defaults to **true**, preserving what every caller
holding its own `Parser` gets today, and the opt-out sits on `Parser.parse(source:)` and
its buffer sibling, which hand back a tree and nothing else. The measurement is
unchanged — the benchmark parses through exactly those entry points — at −2.86%, −2.51%,
−3.02% and −0.17% over two pairs.

**Two things this leaves open.** The compiler's ASTGen constructs `Parser` directly and
never reads the ranges, so it keeps paying until a one-line change there passes
`collectsLookaheadRanges: false`; that is where most of this win actually lives, and it
is a separate `swift` change. And `parseIncrementally` takes no `languageFeatures`, which
is why sourcekit-lsp hand-rolls the parse at all (`091e802f`, "Pass experimental features
to SwiftParser using build settings") — giving it that parameter would let the next
client use the API meant for this instead of reconstructing it.

**What that gate prevents is lost reuse, not incorrectness** — which took a test to
establish rather than reasoning, and the first two attempts at that test passed against
the bug. `IncrementalParseLookup` refuses to reuse a node it has no recorded range for,
so a parse that records nothing produces a correct tree and a correct result; what it
hands the next reparse simply describes none of the nodes it created, and that reparse
re-parses all of them. Nothing fails, nothing is stale, reuse just quietly stops.
`testLookaheadRangesAreRecordedForAnIncrementalParseWithoutAsking` pins it by asserting
that a node the middle parse created is reused by the parse after it; with the gate on
the argument alone it fails with nothing reusable at all.
| ~~P17~~ | | ~~Inline the bump allocator's fast path~~ — `7b2b378a4` | 33 | **dropped**: +3.66% on the declaration-heavy input against `main` |

**P17 is dropped, and its premise is the reason.** The commit marks the bump
`@inlinable` "because the bump is called from other modules", but the only
allocator entry points SwiftParser uses are `RawSyntaxArena`'s wrappers —
`allocateRawSyntaxBuffer`, `allocateTextBuffer`, `allocateNode` — and none of them
is `@inlinable`, on `main` or on this branch. So no other module can see through
to the bump, and SwiftParser's `__text` is byte-identical across the change.
What is left is inlining inside SwiftSyntax, which grows it by 24,596 bytes and
costs 3.66% of the declaration-heavy parse while saving 1.53% of the non-ASCII
one. Profiling shows the work moving rather than shrinking:
`BumpPtrAllocator.allocate` leaves the profile (−2.69pp),
`RawSyntaxArena.intern` enters it (+2.32pp), and `RawSyntax.makeLayout` stops
being a leaf too (−1.63pp), so it cascades past the function it was aimed at.
`@exclusivity(unchecked)` is not implicated: neither side emits a single
`swift_beginAccess`.

Reviving it means making the arena wrappers `@inlinable` so the premise holds,
which pulls `@usableFromInline` onto the arena's internals and is a larger API
change than the 33 lines suggest. The branch measured this at −1.7% / −3.8%, and
that number does not survive contact with `main`. `perf-parser-17-allocator-inline`
(`609875bf7`) holds the attempt.

### Group 6 — collections without an `Array` (chained)

| | | contents | lines | measured |
|---|---|---|---|---|
| [ ] | P18 | Introduce `RawSyntaxNodeList`/`Builder`, generate the buffer initializer, convert `labeledExprList` — `d7ca43ec1` | 245 [867] | −2.1% / −2.4% |
| [ ] | P19 | Remove the `Array` initializer, migrate the remaining 83 sites — `4d63b3595` | 772 [1,275] *mechanical* | **−10.2% / −8.7%** |

The largest win on the branch. P19 is one transformation repeated; its size is
call sites, not ideas.

### The node's header and its tail — cut, and it goes first

`perf-parser-30-tail-alloc` (`ac52caf57`) makes `RawSyntaxData` the header — an
enum over the arena reference whose cases name the shape — and puts that shape's
fields in the same allocation, immediately past it. Three commits: `cde9eead0` does
that, at 411 insertions against 2,325 deletions over 21 files; `442944f70` reads the
tail through one reference, at 189 against 88 over four; and `ac52caf57` allocates it
through one function per shape, at 47 against 38 over two.

| | |
|---|---|
| arena memory | **−8.40%** requested bytes, −7.94% slab capacity |
| tree size | 26.45× the source → **24.23×** |
| instructions | **−1.12% / −1.11%** |
| header | 64 bytes → **8** |
| node | 64 → 56 for a layout node or parsed token, 64 for a materialized one |

It deliberately changes nothing else: the fields keep their types and order, and
a layout node's children and a parsed token's text keep their own allocations.

The second commit gives each shape a `Ref` — a struct holding the pointer to that
shape's fields, as `RawSyntax` holds the pointer to the header — so a field is read
through it rather than through `pointee`, and the text and trivia accessors move
onto it from extensions on the field structs that had no other callers. It measures
**+19k and +66k instructions**, inside the floor, and fingerprints are identical
over the 749 corpus files and 120 corrupted ones. It is here for what comes after
rather than for a number: the shape PRs each add a way to read a tail, and this is
where a parsed token's text accessors go once that text moves into the tail, which
is what makes the same change cost 0.09% when applied to the whole branch instead.

The third turns the three initializers that allocate a node into
`allocateParsedToken`, `allocateMaterializedToken` and `allocateLayout`, each sitting
below the designated factory that calls it. It is naming rather than work — measured
on the integration branch at +18k and −25k, inside the floor — and it separates three
levels that had run together: `parsedToken`, `materializedToken` and `layout` build a
shape's fields, the `make…` functions are what a caller outside the file asks for, and
these three only allocate and initialize. The shape PRs add a fourth token shape and
move a token's text into the tail, so they add parameters to these rather than to a
block of initializers away from every caller.

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

### The parsed token's text and its short shape — cut, requires the header-and-tail PR

`perf-parser-33-parsed-token` (`eeeee643e`) is two commits on the branch above.

`991ee26e3` puts a parsed token's whole text in the node's tail, past the fields,
and has the token store three lengths where it stored a `SyntaxText`: 16 bytes of
base address and count for text the arena already owned, plus the arena's copy of
the whole source that made those addresses valid. The copy into the tail writes
whole units rather than bytes, which is what `textByteCount(for:)` sizes the room
for and `sourceBufferEnd` makes safe — reading the last unit runs past the token,
so that form is taken only where the lexer's buffer is known to extend that far.
The factory takes the lexer's buffer and three byte lengths rather than a
`SyntaxText` and a `Range` built only to be pulled apart, which is where
`0ae93a368` lands.

It also repairs a consumer, which is the part a reviewer will not expect. Collecting
a tree's bytes coalesced adjacent token texts into one append, and that worked only
because every token's text pointed into the arena's copy of the source: a whole tree
was one contiguous run, so a file arrived in a single `append`. Moving the text into
each node ends that, and left unrepaired it is **2.17× the instructions and 1.70× the
time** on the path `SourceLocationConverter` takes for every file. It now allocates
once against the byte length it already knows and copies with `copyText`, which also
retires `withEachSyntaxText(body:)` — no caller, and it cannot say whether a text has
the slack a whole-unit copy needs. 283 insertions against 247 deletions over 11
files.

`eeeee643e` gives the common token its own shape: `SmolParsedToken`, four bytes
for a token that is present, undiagnosed and shorter than 256 bytes, where
`ParsedToken` needs eighteen. The header's case carries the presence and the
absent diagnostic, so the fields need not. Every reader gains a case and the two
paths that give a token a presence or a diagnostic promote it to the full shape.
268 insertions against 29 deletions over 6 files.

| | against the header-and-tail PR | against `main` |
|---|---|---|
| tree memory over the corpus | 24.23× the source → **18.91×**, −21.9% | 26.45× → **18.91×**, −28.5% |
| slab capacity | 241.6 MB → **191.9 MB** | 262.4 MB → **191.9 MB** |
| declaration-heavy | −0.72%, −0.67% | — |
| non-ASCII | −0.51%, −0.57% | — |
| malformed | −1.16% | — |
| collections | −0.79% | — |

Two pairs per figure on the two headline inputs, one each on the other two, under
`swiftlang-6.5.0.12.4`. Tree fingerprints are identical over the 749 corpus files
and the 120 corrupted ones. **The memory is the point** and the instructions are a
by-product: a short token is a quarter of the fields and its text needs no separate
allocation, so a parse asks the arena for a fifth less than the header-and-tail PR
alone.

Both commits build and test on their own, which is worth keeping if they are ever
reordered: the short shape's commit reads the tail the first one laid out.

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

### The layout node — cut, one PR, requires the two above

A non-collection layout node interleaves an `unexpected` slot before its first
child, between every pair and after the last, so *n* children take 2*n*+1 slots.
Over the 749 file corpus **not one of 1,132,225 layout nodes had anything in any
of them** — with every 200th byte deleted it is still under 1% — and those slots
were 56.8% of every layout child slot in the tree. A node keeps room for them only
when it has something to put there.

**One PR rather than the five rows this replaces.** P23 through P27 were staged as
separate reviews, and that staging does not survive contact: P23 is a header case
with both shapes still identical, P24 a generated `SyntaxKind` property, and neither
does anything until P25 changes what a node stores. P25 cannot be split from its
mutation tests, and P26 and P27 only pay because P25 moved the children. Landing
them apart means a reviewer reads the same slots three times and measures noise
twice.

`perf-parser-35-compact-layout` at `7aa4d8bfc`, seven commits over 27 files. It was
ported rather than cherry-picked: the commits it comes from predate a token's shapes,
so the layout work is re-expressed against the shapes the parsed-token PR leaves
behind.

| | commit | what it is |
|---|---|---|
| 1 | `dd36b5a9f` | children into the tail, the two extra header cases, the storage mode, the two builders, validation through `logicalChildren` |
| 2 | `f11f0d4b6` | the mutation tests |
| 3 | `36bad794a` | the three source-order walks read the slots a node kept |
| 4 | `11c26c9f8` | the generated raw accessors reach a child by where it sits |
| 5 | `dce32744a` | a node's `SyntaxData` buffer written from the slots it kept |
| 6 | `3edb3dd87` | a flat node's slots read without asking its kind |
| 7 | `7aa4d8bfc` | the data buffer's two shapes split, so what they call stays inlined |

**Measured against its own base**, two independent builds per side: the tree over the
corpus 182.3 MB → **97.8 MB**, which is 18.91× the source down to **10.14×**; a parse
**−3.4%** on the declaration-heavy input and **−3.2%** on the non-ASCII one, three
pairs agreeing within 0.03%. All 749 corpus fingerprints unchanged, walking every node
with `viewMode: .all`.

**Two commits here exist because compacting a node's slots taxes everything that
reads them, and neither cost was visible until the instrument was fixed.** A reader
that goes through the positions a kind names pays a bounds check, a branch and a
division for each one, on a node that no longer stores them:

| against the pre-compaction base | without the repair | with it |
|---|---|---|
| collecting a tree's syntax text | +57% | −7.5% |
| `SourceLocationConverter` | +36% | −4.9% |
| `description` | +12% | −1.0% |
| an empty `SyntaxVisitor` walk | +18.7% | **−1.4%** |
| reading a tree through its typed accessors | +6.5% | **−0.1%** |
| reaching every child through `children(viewMode:)` | +1.4% | **−1.1%** |

The first three are what `36bad794a` repairs, in the walks themselves. The last two
are what `dce32744a` repairs, in `SyntaxDataArena`: every `Syntax` child is reached by
its index in the layout as the tree describes it, so each node gets a buffer with an
entry per position its kind names, and filling it by asking `children` per position is
where a client's cost went. Writing it from the two regions a node keeps removes that
without changing a single index a client uses.

**A parse is unaffected by any of them** — it builds no `SyntaxData` and walks no tree —
so the parse figures above hold with all three repairs in place.

**The third repair is `7aa4d8bfc`, and it was an inlining regression rather than a
design one.** After the first two, a reader still paid 3.3% on a visitor walk, and a
profile named the cause: `AbsoluteSyntaxInfo.advancedBySibling` had its own frame on
this branch and none at all before it. It is `internal`, so a symbol for it means it is
called rather than inlined, and the reason is that the function calling it had grown —
both buffer shapes in one body, `createDataImpl` inlined into each, 766 instructions
against 271 — until the inliner stopped taking a five-line function that runs once per
slot of every node. Splitting the shapes into two functions and marking that one
`@inline(__always)` closes the gap, and takes all three read paths slightly below where
they were before the compaction.

**What the earlier −4.1% and −6.5% were.** They were measured through a benchmark
that dispatched on the typed enum and then recursed through `children(viewMode:)`,
which is the generic walk, and asked a collection only for its `count`. The
accessor path it was named after was a minority of what it measured. Rewritten to
recurse through the accessors and iterate each list as a `SyntaxCollection`, it puts
`11c26c9f8` within its noise and shows what the table above shows. The rows below are
kept as a record of what the parts measured on the branch they were developed on.

| what it contains | drawn from | measured |
|---|---|---|
| children into the node's tail | `64487d0b4`, `bb1f9a521` | part of the tree figures below |
| a collection's own header case, and field accessors made exhaustive | `f89090804`, `be5232589` | neutral |
| generate whether a kind interleaves its unexpected children | `e7474384d` | — |
| no room for `unexpected` children in a node that has none, with the mutation tests | `716127f54`, `587968bf9` | **tree −26%**, parse −1.5% / −1.7% |
| reach a child by where it sits, not by where the tree says | `0f3933e09` | reads −4.1% |
| one flat case, and read its slots without a test | `b9922d00d`, `a05c1a083`, `d5e8375cd` | reads **−6.5%** |
| the caller says which storage a node has, rather than the builder asking the kind | `f6222e8a6` | neutral; removes a 241-case switch from every node |
| one function builds every layout node; `makeEmptyLayout` and the designated factories go | `7f004f8f4`, `f5f720864`, `1ec652738`, `85ead50c1` | neutral, −190 lines |
| validation follows the children as the tree describes them | `d98869d1f` | restores a configuration that had been checking nothing |
| the two walks that read a node's children read the slots it kept | `130cfe568`, `bd0697ab7` | `syntaxTextBytes` −34%; `description` and the line scan flat |

**P22 first, and not as a courtesy.** The read figures above are the ones this PR
exists for, and nothing else in the repository reads a tree through the generated
accessors, so without P22 they measure as noise. It counts instructions rather than
time, which is what resolves an effect under a percent.

**Two things a reviewer will want, and neither is in the diffs.** `RawSyntaxData`
gains three shapes where it had one, and the checked field accessors ended in
`default:` arms the compiler could not flag — which is why the accessors are made
exhaustive before any shape is added. And nearly all of the read-path gain is *not*
asking `SyntaxKind` a question the header answers: `isSyntaxCollection` and
`interleavesUnexpectedChildren` are switches over three hundred kinds that sat on
per-node paths, which is why merging the flat cases was worth more than every other
read-path change together.

**The mutation paths are the risk.** Every mutating operation hands its layout back
to `makeLayout`, which decides the shape afresh — that is what keeps a rewritten node
compact and what let `SyntaxRewriter` go untouched. Landing the compaction without
that would silently re-expand every rewritten tree, so `587968bf9` travels with it.

### Group 9 — lookahead allocations (standalone, independent of everything else)

Attributing every retain, release and allocation to its caller put reference
counting at 13.3% of a parse, of which 9.6% was `Array` machinery — and half of
that was in lookahead. Neither of these is an algorithm change; both are an
allocation that did not need to happen.

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P28 | Push a skipping state without allocating an array to hold it — `a5ac88b83` | 24 | **−2.4%** declaration-heavy and flat non-ASCII vs `main`; −1.6% / **−3.9%** / −0.7% at its own base |
| [x] | P29 | Ask a spec set for its cases once — `3ce750382`, reverted in `cb62d8055`, re-applied as `a196f3daa` | 14 | **−1.2% / −0.84%** vs `main`, against −2.0% / −1.3% at its own base, all in retired instructions |

Percentages are collections, declaration-heavy and non-ASCII, each against the
commit's own parent. The spreads are opposite and that is the point: skipping
costs the declaration-heavy input most, recovery costs the collections one most.

`Lookahead.skip(initialState:)` pushed onto its state stack with
`stack += [a, b]`, which builds a temporary array for every push, on the path
malformed input and every speculative parse take. `canRecoverTo(anyIn:)` asked
`specSet.allCases` three times — four with alternate token introspection enabled,
which is why the hoist has to go above that `#if` — and each call builds a fresh
`Array`, one of which it then reduced through a second array it discarded.

Measuring the two against `main` sharpened both. Nearly all of P28 is the `+=`
rewrite and next to none of it is the capacity: reserving it, measured on its own,
is 0.04%, because growth was never the cost — `skip(initialState:)` calls
`swift_allocObject` six times, once per push site, where appending twice calls it
not at all. Instrumenting the peak depth per call is what put the reservation at 8:
over 749 files the deepest stack is 7 and 9,043 of the 9,059 calls reach 1 or 3,
while corrupted input goes as deep as 55 and grows there as it did before. And
skipping is not a recovery path in any useful sense — the declaration-heavy input
makes 625 of its 1,362 calls for the 625 attributes that carry an argument, which
is why that input is the one that gains.

P29's shape is load-bearing rather than stylistic. Writing the `lazy.map` as
`\.spec.recoveryPrecedence` costs 33.7M instructions on the declaration-heavy input
and 20.3M on the non-ASCII one — 24% and 17% of a parse, twenty times what the
hoist saves, and enough to make the change a 23% regression against `main` — under
swiftlang-6.5.0.12.4, which still carries rdar://186588859.

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

### Keyword lookup by the bytes as an integer — cut off `main`

`perf-parser-36-keyword-lookup` (`616abc45f`), two files: the template and the generated
`Keyword.swift`. Off `e9289aa44`, independent of everything else here, and on the
integration branch as `20e87eccf`.

`Keyword.init(_ text:)` switches on the text's length, then over the keywords of that
length as string literals. That second switch compiles to a chain of byte comparisons
that **reloads the text for every candidate it rejects** — 48 loads in the length-6
initializer — and `lexIdentifier` asks for every identifier in a file, so a miss walks
the whole bucket. Profiling a release parse put the lookup at **3.1% of leaf samples**,
with `_length6` the most expensive bucket.

Reading the bytes once into a `UInt64` and switching on that integer gives the compiler
something it can search. Measured, two pairs agreeing within 0.03 points: **−2.21%** on
`MinimalCollections`, **−1.32%** on the declaration-heavy input, **−1.04%** on the
non-ASCII one and **−2.56%** on the corrupted one. Lengths above eight keep the text
switch; the loads tell the story:

| | `main` | packed |
|---|---|---|
| `_length3` | 111 instructions, 24 loads | 89, **2** |
| `_length4` | 169, 24 | 175, **1** |
| `_length6` | 245, 48 | 210, **3** |
| `_length8` | 236, 26 | 265, **1** |
| `_length10` | 136, 22 | unchanged |

Some buckets gain instructions while losing loads, which is the trade taken.

**One shared table for every short keyword is worse, measured, and the depth is why.**
The packed value identifies a keyword without its length — a shorter keyword's unset
bytes are zero, and no keyword ends in a zero byte — so the eight per-length tables can
be one, with `Keyword.init(_:)` rejecting text that ends in a zero byte to keep
`"let\0"` from answering as `.let`. It measures **half the win**: −1.43%, −0.74%, −0.62%
and −1.24% against −2.21%, −1.32%, −1.04% and −2.56%. One table of 136 values is about
7.1 comparisons deep where eight of about 17 are 4.1, and the switch on the length that
picks between them is a jump table costing nearly nothing. Fewer, larger tables buy
instruction cache and pay for it in depth, and depth wins here. Dropped, and with it the
precondition, which only the shared table needed.

**Ordering the cases by frequency is not worth trying on top of this**, which it would
have been before: LLVM sorts case values when lowering a `switch`, so the emitted code is
a binary search over ordered values while the generated source stays alphabetical. Source
order no longer reaches the machine code. Biasing toward common keywords would also be
the wrong trade, since every identifier misses and a balanced search costs about five
comparisons either way.

### Not yet assigned to a PR

Work that landed after this plan was written and has no row above. None of it is
large; it needs homes rather than analysis.

| | where it belongs |
|---|---|
| ~~`0ae93a368` Derive a lexeme's `start` from the cursor it was lexed from~~ | **folded into `991ee26e3`**, the parsed-token PR: the factory takes the lexer's buffer and lengths, which is the same argument about not storing what the cursor answers |
| `970d1a7ac` Scan the run of ordinary bytes inside a string literal — −10.7% on the declaration-heavy input | its own PR; independent of everything, and the third instance of the run-scanning shape |
| `e12075211` Stop tracking `Parser`'s size | fold into P5, which is the PR that introduces the tracking; `Parser` gains stored properties under `SWIFTPARSER_ENABLE_ALTERNATE_TOKEN_INTROSPECTION`, so one expected number cannot describe it |
| `7577f33f0` Report the first lexeme of a file as beginning a line | **its own PR, stacked on `perf-parser-32-position-compaction`.** It seeds the flag from `isAtStartOfInput`, which is that branch's invention — main's cursor takes the previous byte instead, so cutting this off main means writing the seed as `previous == "\0"`, which is what main's own `isAtStartOfFile` and conflict-marker check already use. Holding for 32 keeps the commit verbatim. Its 117 updated expectations apply to main's test file unchanged. No tree changes — fingerprints over 722 files and 112 snippets written to start at offset 0 are identical, because every reader of the flag and all 57 `allowAtStartOfLine: false` specs sit after something has been consumed |
| `c01c36234` List the added sources in the CMake builds | **split across the PRs that add those files** — P5 for `MemoryLayout.swift`, Group 6 for `RawSyntaxNodeList.swift` and `RawSyntaxNodeListBuilder.swift`. A PR that adds a file and not its CMake line breaks the CMake build while SwiftPM stays green |

## Needs your sign-off

- [x] **P16** no longer changes observable behaviour: `collectsLookaheadRanges`
      defaults to true, so a caller holding its own `Parser` sees what it saw before,
      and only `Parser.parse(source:)` — which returns a tree and nothing else — opts
      out. Settled by 3447 going red on sourcekit-lsp; see Group 5.
- [ ] **P19** removes an initializer from every collection node under
      `@_spi(RawSyntax)`. Nothing outside SwiftParser used it.
- [ ] **The header-and-tail PR** (3426) changes `RawSyntaxData`'s layout and puts
      every token's fields behind a pointer, which is visible through
      `RawSyntaxTokenView`.

CI has `api_breakage_check_enabled: false`, so none of these trip a check
automatically. They want saying in prose.

## Suggested order

1. **P16** is up as 3447 on `e9289aa44`, measured at −3.8% / −3.1% / −3.6% / −0.1%.
2. **P3**, on `e9289aa44` as `4c132607d` and measured there at −1.9% / −2.0% / −1.3% /
   −3.7%. One commit, nine lines, one file. Ready to post.
3. **The Cursor/Position split**, rebased onto `e9289aa44` as `f568c63ed` and measured
   there at −0.3% / −0.5% / −2.3% / −1.5%. Whether six commits touching the lexer's core
   are worth that is a judgement call; the non-ASCII input is where it earns its keep.
4. **The header-and-tail PR** (3426). Everything below assumes it.
5. **The parsed-token PR**, cut and measured: the tree from 24.23× the source to
   18.91×, the parse 0.5% to 1.2% faster depending on the input. It sits on 3426 and
   shares `Cursor.swift` and `Parser.swift` with 3425, so it wants that merged first.
   Its two commits can be reviewed in order — the text into the tail, then the
   four-byte shape — and each builds and tests on its own.
6. Groups 3 and 4 in parallel with the above where they do not collide; P11+P12 is
   upstream, so P13, P18 and P19 are free of it.
7. Group 6 last among the parser work: it is the largest, touches CodeGeneration
   and most parser files, and wants a quiet base.
8. **The layout PR** after the header-and-tail and parsed-token PRs. All three
   reshape `RawSyntax.swift`, and it is cut on top of the parsed-token branch, so it
   goes out once that one has. Its read figures are measured through the benchmark
   3437 put upstream, so they can be reproduced by anyone.
9. Group 9 whenever convenient. Two small diffs in two files, dependent on
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
