# Merging `productize-raw-x-syntax` into the compaction work

`2b71b190e` — *[SwiftParser] Move typed raw syntax nodes into SwiftParser* — sits on
`origin/main` (`717dc9745`) and moves the typed `Raw*Syntax` nodes, their
`RawSyntaxNodeProtocol`, and the template that generates them out of SwiftSyntax
and into SwiftParser. 48 files, mostly renames.

Cherry-picked onto `perf-parser-2026-woc` (`c01c36234`) it conflicts in 15 files.
That number overstates the work: nine of them are generated.

## The conflict surface, as measured

| file | conflict | resolution |
|---|---|---|
| `Sources/SwiftParser/generated/raw/RawSyntaxNodes*.swift` (9) | renamed on their side, rewritten on ours | **regenerate**, do not merge |
| `templates/swiftparser/RawSyntaxNodesFile.swift` | 1 hunk | real merge — their move, our rewrite |
| `Sources/SwiftSyntax/Raw/RawSyntax.swift` | 1 hunk | real merge |
| `Sources/SwiftSyntax/Raw/RawSyntaxLayoutView.swift` | 1 hunk | real merge |
| `Sources/SwiftSyntax/Raw/RawSyntaxTokenView.swift` | 3 hunks | real merge |
| `Sources/SwiftSyntax/CMakeLists.txt` | 1 hunk | their deletions plus our `Raw/RawSyntaxNodeList.swift` line |
| `Tests/SwiftSyntaxTest/RawSyntaxTests.swift` | `UD` — they delete, we modified | decide where those tests live |

Seven hunks of genuine merging. The nine generated files are derived from the one
template, so resolving them by hand would be both laborious and wrong.

## What attempting it found, which the conflicts do not show

An attempt is preserved at `scratch-raw-merge` (`4f20a52d6`). Everything above
resolved, the generator wrote the nine files to their new paths without complaint —
**and it does not compile.** The real work is not merging text, it is deciding
which side of the new module boundary the things this branch added belong on.

1. **`RawSyntaxNodeList` cannot stay in SwiftSyntax.** It is generic over
   `RawSyntaxNodeProtocol`, which the move takes to SwiftParser, so the type the
   collections work introduced has to move with it — along with its CMake entry,
   and with consequences for how P18 and P19 are cut.
2. **SwiftSyntax still reaches for typed raw nodes.** `RawSyntaxTokenView` uses
   `RawTokenSyntax` and `.cast`, which are no longer in the module. This is in code
   the compaction work also changed — `withPresence` and `rebuiltParsedToken` — so
   their handling of it and ours have to be reconciled rather than picked between.
3. **The `raw.header` versus `header` hunks cannot be resolved by rule.** Dropping
   the prefix is correct inside `extension RawSyntax`, where the move removes the
   conformance that supplied `raw`, and wrong inside `RawSyntaxTokenView`, which
   holds its own `raw`. Resolving all five the same way is what broke the build.
   Read them one at a time.

So the estimate above — seven hunks, a couple of hours — is wrong in kind, not in
size. Budget for a module-partitioning decision, and expect it to touch the
collections work as well as the compaction.

## Order to do it in

1. **Take the renames.** Their paths win: the generated nodes and their template
   move to SwiftParser.
2. **Merge the template.** Their side changes the module it belongs to; ours
   rewrote what it emits — real children reached by `realChild(at:)`, unexpected
   slots by `unexpectedSlot(at:)`, initializers taking `childCount:hasUnexpected:`
   and writing each slot exactly once with `initializeElement(at:to:)`, and
   collection initializers passing `hasUnexpected: false`. Ours is the content,
   theirs is the location.
3. **Regenerate**, and let the generator write the nine files at their new paths:
   `swift run --package-path CodeGeneration generate-swift-syntax`. Confirm the
   working tree is clean afterwards, which is the check that the template and the
   files agree.
4. **Merge the three SwiftSyntax files.** Ours is the compaction — the header cases,
   `RawLayoutChildren`, `RawSyntaxElements`, `flatSlots`, the exhaustive field
   accessors. Theirs is what the move needs: visibility widened for cross-module
   use, and `RawSyntaxNodeProtocol` no longer being in the same module. Keep ours
   and re-apply theirs on top; nothing in their diff touches the shapes.
5. **Both CMake lists.** SwiftSyntax loses the generated raw files and keeps our
   `Raw/RawSyntaxNodeList.swift`; SwiftParser gains them. Then re-run the audit
   over every module — files changing module is exactly the case that broke CMake
   silently once already, and SwiftPM will not notice.
6. **Decide where the raw tests live.** They delete
   `Tests/SwiftSyntaxTest/RawSyntaxTests.swift`; we changed it. If the typed raw
   nodes are in SwiftParser then the tests belong in `SwiftParserTest`, and
   `Tests/SwiftSyntaxTest/CompactLayoutTests.swift` should be checked for anything
   that reaches for a typed raw node.

## The performance risk, which is the reason to measure rather than assume

The move puts a **module boundary** between the generated accessors and the
functions they call. Today `makeLayout`, `realChild(at:)`, `unexpectedSlot(at:)`
and `RawSyntaxElements` are same-module calls from generated code, and a
whole-module build inlines them; afterwards the generated code is in SwiftParser
and those become cross-module calls into SwiftSyntax.

That matters here more than it would elsewhere, because three separate results in
this work turned on inlining placement: the bump allocator's fast path was worth
1.7% to 3.8% only once `@inlinable`, `advanceValidatingUTF8Character` needed
`@inline(__always)` for its own fast path to pay, and the hand-written ASCII path
in `advance(if:)` existed only because the function under it was not being
inlined. The dylib profile taken through `swift-parse-test` also shows the same
sources behaving differently once modules are separated.

The direction is now genuinely unclear rather than merely unmeasured, because two
effects pull opposite ways: the raw node accessors start crossing a module
boundary, while `RawSyntaxNodeList`-based collection building stops crossing one
if it moves to SwiftParser. Do not predict the sign.

**What to measure, after the merge and before believing it:**

- The three inputs, two builds per side, wall clock — the compaction's own
  numbers were −1.5% to −1.7%, so a regression of that size is what to watch for.
- `AccessorPerformanceTests`, warm median of four runs with the first discarded.
  This is the instrument that sees reaching a child at all.
- A profile, checking specifically whether `realChild(at:)`, `unexpectedSlot(at:)`
  or `makeLayout` appear as call frames rather than inlined code.

**If they do appear**, the fix is `@inlinable` on that small set rather than
abandoning the move: they are a handful of functions, each a load or a compare, and
they were only ever cheap because they inlined.

## Verification checklist, unchanged from the rest of this work

749-file corpus fingerprint and the 120 corrupted files against the pre-merge tip;
trivia, UTF-8 and incremental checks; the suite; Address Sanitizer over both
corpora, since the merge touches tail arithmetic; the arena memory probe, which
should be **identical** — the move changes no shape, so any change in tree memory
means something went wrong.

---

## Attempted, measured, and deferred

Resolved and committed at `1391321b8` on `scratch-raw-merge`: builds, suite 3,486
passing, trees identical to the pre-merge tip over the corpus and the 120 corrupted
files, Address Sanitizer clean on both, and **tree memory byte-identical**, which is
the check that the move altered no node shape.

And **2% to 4% slower**: 1.641 → 1.671 ms on the collections input, 3.684 → 3.803 on
the declaration-heavy one, confirmed at 3.540 → 3.681 on a second run. Not carried
onto the integration branch on that basis; the refactor has not landed upstream, and
the inlining question is better settled against it than against a cherry-pick.

**The read-path instrument is blind to this.** `AccessorPerformanceTests` measured
−0.09%, inside the noise floor, and on that basis this merge was described as
costing nothing. That was wrong: the test reads trees through typed accessors, and
the regression is in *building* them. Do not clear a change on that instrument alone
when the change touches construction.

The profile says exactly what happens, on the declaration-heavy input:

| leaf | pre-merge | merged |
|---|---|---|
| `RawSyntax.makeLayout(kind:childCount:hasUnexpected:…)` | 0.00% | **12.18%** |
| `RawSyntax.parsedToken`, specialized | 5.31% | 0.00% |
| `RawSyntax.parsedToken`, **unspecialized** | 0.00% | 4.55% |
| the generated `Raw*Syntax.init`s | ~3.0% together | 0.00% |
| `<deduplicated_symbol>` | 4.32% | 1.84% |

One mechanism: `makeLayout` and the generated initializers were inlined into each
other and appeared as no leaf at all; across the module boundary they are real
calls. `parsedToken` additionally loses its *specialisation*, which every token
pays. `<deduplicated_symbol>` shrinks because the merged generated bodies that were
being folded together no longer exist.

So `@inlinable` on `makeLayout` alone cannot fix it — it would not recover
`parsedToken`'s specialisation — and `@inlinable` on `makeLayout` already demands
`@usableFromInline` on about a dozen internals including `RawSyntaxData` itself, its
`Layout` initializer, `RecursiveRawSyntaxFlags` and four of its cases,
`arenaReference`, `addChild`, `byteLength32` and `totalNodes32`. That is most of the
node representation. Cross-module optimisation is the better lever, or waiting.
