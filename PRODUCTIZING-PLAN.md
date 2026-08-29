# Productizing `perf-parser-2026-woc`

Splitting 51 commits into reviewable pull requests. Parsing is 2.56×/2.40× faster
and the tree is a quarter smaller; see PERFORMANCE-REPORT.md for what each change
did and why.

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

- [ ] `6e5ee4ee4` + `ad179aa76` + `8886b84d0` + `9a9c7095c` → one commit. The
      state stack became a pointer and a count, then a linked list, then an
      interned one. Only the end state is worth reviewing.
- [ ] `aad644153` + `c331d96de` + `d3952537f` → one commit. The same field held
      three ways: `unowned(unsafe)`, then boxed for SPI, then `Unmanaged`.
- [ ] `ffa99ce81` + `43ad5af60` → one commit. The narrowing introduced a 2%
      regression that the next commit fixes; the first alone is a regression.
- [ ] `d64f96239` + `c2a9dffe8` + `916c0b86b` + `7524ff0b4` + `3077fc191` → one
      commit. The last two reshape what the first three wrote.
- [x] `79bc75d3d` + `50044b0fe` + `e3ff94452` → one commit. The middle one adds a
      `continuesAnIdentifier` to `Cursor.swift` that the last one deletes, moving
      the classification to `CharacterInfo.swift` where it ends up.

**Drop.**

- [ ] `fc282de88`. It documents `PrepareForKeywordMatch`, which the next commit
      deletes. It exists only because I misread the code.

**Leave out.** The nine report commits, about 1,150 lines. PERFORMANCE-REPORT.md
is a working document that cites branch-local hashes and my own measurement
mistakes; it is not something the project should carry. Keep it to draw PR
descriptions from.

## Progress

Built, verified and measured against `main`: P1, P2, P3, P4, P5+P6, P7, P10,
P14, P15 — ten of 21, all of Group 1 and the front of Group 2. One commit each
except P5+P6, which is two. None pushed.

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
| [ ] | P8 | State stack as a shared linked list — *squash of 4* | ~250 | −1.9% / −1.9%, then +0.6% for interning |
| [ ] | P9 | Hand the lexer its allocator without retaining it — *squash of 3* | ~150 | −4.0/−3.6, then −1.7/−1.5 |

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
| [x] | P10 | Cache the resolved keyword on `Lexeme`, reuse `lexIdentifier`'s lookup — *squash of 2* | 79 | **−6.5% / −6.6%** vs `main`, against **−10.3/−9.8** claimed at its own base |
| [ ] | P11 | Match hand-written spec sets on the keyword — *squash of 5* | ~700 *mechanical* | −9.8/−7.8, −0.4/−1.2, −2.5/−2.3 |
| [ ] | P12 | Generate spec set initializers the same way — `eca3c7bef`, `2ac6a490b` | 150 [2,645] | −0.3% / −0.3% |
| [ ] | P13 | Don't declare attribute names as keywords — `41a10b37b` | 250 [108] | neutral |

P11 and P12 are one pattern repeated across 117 spec sets. P13 is independent of
the rest of this group.

### Group 4 — character scanning (independent of each other)

| | | contents | lines | measured |
|---|---|---|---|---|
| [x] | P14 | Trivia: decide before consuming, then the fast path — *squash of 4* | 133 | **−9.1%/−10.3% and −10.5%/−10.9%** vs `main`, two builds per input |
| [x] | P15 | Identifier scanning and one character classification — *squash of 3* | 96 | **−10.3% / −9.3%** vs `main`, against −3.1/−3.2 claimed across its own bases |

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
`b193016db` converts twenty snapshots from cursors to positions.

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

### Tail allocated nodes — a PR of its own, after Group 7

`64487d0b4` makes a node a one-word header followed by its own shape's fields and
then its children or its text, which supersedes the question Group 7 was
answering. It is 744 insertions over seven files, one commit, and it cannot be
split without reconstructing intermediate states in a style the final one
replaced — the two attempts at that would each have shipped something either
broken or memory-regressing.

Worth **6.2% / 4.9%** of parse time and takes the tree from 20.90× the source to
15.36×, counting allocator padding. It reverts `1f6c6234f`'s whole-source copy
without reintroducing the per-token allocation that made `748dde4ff` slow, since
the text now lands in an allocation the node was making anyway.

It must follow Group 7: `77a7fc600` and `ffa99ce81` shrink the payload enum this
change deletes, and their commit messages explain the layout reasoning it builds
on. Landing them in the other order would leave the earlier two looking pointless.

Needs saying in the PR: it removes `RawSyntaxData.Payload`, the stored form of a
layout node's fields, and `RawSyntax.rawData` from the `@_spi(RawSyntax)` surface,
and it adds a deliberate bounded over-read, checked under AddressSanitizer over an
exactly-sized-allocation sweep now in `testParseBufferEOFEdgeCases`.

### Group 7 — tree memory (chained, SwiftSyntax only)

| | | contents | lines | effect |
|---|---|---|---|---|
| [ ] | P20 | Hold a materialized token's fields behind a pointer — `77a7fc600` | 106 | node 64 → 56 bytes |
| [ ] | P21 | Narrow the node's fields and reorder them — *squash of 2* | ~250 | node → **40**, tree 26.8× → **20.0×**, ~0.5% slower |

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

1. Group 1, in any order. Cheap to review; P2 is the only one of the four worth
   a performance claim.
2. Groups 2, 3, 4 and 7 in parallel — 2 and 3 touch different files, 4 is
   independent of both, 7 is a different module.
3. Group 5 once the two questions above are settled.
4. Group 6 last: it is the largest, touches CodeGeneration and most parser files,
   and wants a quiet base.

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
