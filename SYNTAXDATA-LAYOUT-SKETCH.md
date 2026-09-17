# Sketch: what `SyntaxData` costs, and three ways to shrink it

The raw tree is 10.14× the source it came from, down from 26.45×. The `Syntax`
layer above it has had none of that attention, and it is now the larger of the
two for a client that walks a whole file: a tree read through its typed
accessors allocates `SyntaxData` for every node it touches and a pointer array
for every layout node's children.

This is a sketch, not a plan. The arithmetic below is exact per node; the corpus
totals are estimated from a census that does not include absent slots, and the
first thing any of this needs is a probe on `SyntaxDataArena` like
`harness/arena-probe.patch.swift` is for the raw arena.

## What a node costs today

`SyntaxData` is 32 bytes with no padding:

| field | bytes | |
|---|---|---|
| `raw` | 8 | pointer into the raw arena |
| `parent` | 8 | pointer to the parent's data |
| `absoluteInfo` | 12 | `offset`, `layoutIndexInParent`, `indexInTree`, 4 each |
| `childCount` | 4 | cache of `raw.layoutView?.children.count ?? 0` |

A layout node adds 8 bytes of tail for an `AtomicPointer`, which is where the
children buffer goes when someone first asks for it, and then that buffer:
**8 bytes per position the node's kind names**, one `SyntaxDataReference?` each.
The node's own children are separate 32-byte allocations, one per present child.

The design says so itself, in `slabSize(for:)`: it budgets
`dataSize + (dataSize + pointerSize * 4)` per node — 32 for the data, 32 for its
share of pointer arrays.

**The buffer is still logical.** Compacting the raw tree stopped storing a slot
for an `unexpected` child that does not exist, but `childCount` here is
`RawLayoutChildren`'s count, so a node whose kind interleaves gets 2n+1 pointers
for n children and n+1 of them are permanently nil. Over the corpus not one of
1,132,225 layout nodes had anything in any of those positions.

For a node with 3 children that interleaves: 32 + 8 + 8×7 = **96 bytes**, of
which **32 are pointers to positions that cannot hold anything**.

Corpus scale, if a client visits everything: 2,802,769 nodes, 1,132,225 of them
layout nodes. At ~3.4M declared child positions the pointer arrays come to
roughly 63 MB against 90 MB of `SyntaxData` — call it **160 MB for a 9.6 MB
corpus**, against 98 MB for the raw tree it describes.

## M1 — make the buffer dense

Store as many entries as the node keeps slots, not as many as its kind names: n
for a node with nothing unexpected in it, 2n+1 for one that has something. This
is the same change the raw tree already took, one layer up, and it removes both
the memory and the nil stores that go with it.

The buffer must stay **source-ordered**, because `SyntaxChildrenIndex` is
`Comparable` and its order is the order children appear. So a dense buffer holds
the children in order, and an interleaved node keeps its 2n+1 shape — which is
under 1% of nodes.

What has to move with it:

- `Syntax.child(at:)` takes a logical index from the generated accessors
  (`child(at: 15)`). It becomes a conversion: on a dense node, logical 2k+1 is
  physical k — a shift after one test of the header word.
- `SyntaxChildren` iterates the buffer, so its indices become physical. They stay
  source-ordered, and `SyntaxChildrenIndex.value` is internal.
- `indexInParent` must keep returning the **logical** index, because
  `keyPathInParent` indexes a generated table with it and `SyntaxRewriter` writes
  `newLayout[layoutIndexInParent]`. Both indices are needed; `absoluteInfo` has
  room for the second.

Estimated: pointer arrays 63 MB → 27 MB, so **−22% of the layer**.

## M2 — put the children in the array, not pointers to them

A parent allocates a buffer of pointers, then allocates each child's data
separately. Both happen at the same moment — `createLayoutDataImpl` builds every
child of a node at once — so the pointer array is an indirection with no
laziness to justify it.

Allocate instead one contiguous run of `SyntaxData` for the node's slots. Child k
lives at `base + k * stride`; the `AtomicPointer` in the parent's tail points at
the run. The array of pointers disappears: **8 bytes per slot and one dependent
load per child access**, and a node's children become one allocation rather than
1 + n.

Two things this needs:

- **A tombstone for an absent slot**, which today is a nil pointer. `childCount ==
  UInt32.max` would do, or a spare byte once `parent` goes (below).
- **Absent slots now cost a whole `SyntaxData`** where they cost 8 bytes before.
  With ~0.6M absent positions over the corpus that is +14 MB against −27 MB.

**`parent` can then be arithmetic rather than a field.** A child knows its
physical index; the run's base is `self - index * stride`, and a 16-byte header
before the run holds the parent reference and the count. That is 8 bytes back on
every node in the tree — 22 MB over the corpus — for two instructions in
`.parent`, and it takes `SyntaxData` to 24 bytes with its alignment intact.

Estimated with M1: **160 MB → ~100 MB, −38%**, and fewer allocator calls on every
path that reads a tree.

## M3 — narrow the references

If a tree's data were one contiguous region, every reference in it could be a
32-bit offset instead of a pointer: `SyntaxData.raw` cannot, because raw nodes
come from arenas that `addChild` may have attached from elsewhere, but the run
header's parent reference and any remaining `SyntaxDataReference` could.

`SyntaxDataArena` already sizes its first slab to hold the whole tree, so the
common case is contiguous; the uncommon case is not, and a `Syntax` that holds an
offset would have to resolve it against a base that can move. That trade —
4 bytes per reference against a load per dereference — is worth measuring only
after M1 and M2, which do not need it.

## Order, and what to do first

1. **Probe the arena.** Bytes actually advanced per tree, split into `SyntaxData`,
   tails and buffers, for the four benchmark inputs. Everything above is arithmetic
   until this exists; the corpus estimate could be off by a third.
2. **M1**, which is contained: one buffer shape, one conversion in `child(at:)`,
   and the second index in `absoluteInfo`.
3. **M2**, which is the real win and the real work: it changes what a
   `SyntaxDataReference` points at.
4. **M3** only if the probe says the remaining references matter.

## How it gets verified

- `corpusdump` fingerprints over the 749 files, walking `viewMode: .all`, which
  covers children, order, absent positions and node counts.
- `readbench` for the three read paths and `measure-memory` for the arena, both
  ends built in one session.
- The invariants that are not fingerprints: `indexInParent` and `keyPathInParent`
  agree with the generated tables; `SyntaxIdentifier` is stable across `detached`
  and re-rooting; `SyntaxChildrenIndex` ordering matches source order; a rewritten
  node's children match one built outright, which `CompactLayoutTests` already
  checks one layer down.
