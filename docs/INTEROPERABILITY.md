# Interoperability with CombinatorialRigidity

This repository and Bryan Gin-ge Chen's
[CombinatorialRigidity](https://github.com/bryangingechen/CombinatorialRigidity)
use the same graph-theoretic separation:

- a body-level multigraph has an independent type of edge occurrences;
- an expanded bar--joint framework is a mathlib `SimpleGraph`.

The compatibility surface uses CombinatorialRigidity commit
`581c0112c91fddc125f6990ebe04256829839413`. The graph adapter is checked in the
main Lean 4.29 project. The rank comparison is checked in a separate Lean
4.34.0-rc2 package that imports CombinatorialRigidity directly.

## Body-level multigraphs

Import `RB31Interop` to obtain

```text
RB31E2E.LooplessMultiGraph.toGraph
RB31E2E.BodyPinIncidence.toGraph
```

For `H : BodyPinIncidence`, the graph `H.toGraph : Graph H.Body H.Pin`
has the full vertex and edge sets. Its link relation is

```text
H.toGraph.IsLink e u v ↔
  (H.left e = u ∧ H.right e = v) ∨
  (H.left e = v ∧ H.right e = u).
```

Thus isolated bodies remain vertices and parallel pins remain distinct edges.
The equivalence `H.pinEquiv` identifies `H.Pin` with the edge subtype of
`H.toGraph`. The accompanying lemmas expose vertex membership, edge membership,
adjacency, and looplessness without adding a dependency on
CombinatorialRigidity.

This conversion identifies the incidence data. A pin imposes different
constraints from a body--bar edge, so rigidity statements continue to use the
expanded bar--joint graph below.

## Expanded bar--joint graphs

The expansion `H.bodyPinGraph extra` is already a mathlib `SimpleGraph`.
No graph conversion is needed at this layer. A pin is an edge of the body-level
incidence graph and a vertex of the expanded graph; the two roles are kept
distinct.

## Generic rank

In this repository, generic bar--joint rank is the largest row rank achieved by
a real placement. In CombinatorialRigidity it is defined as the rank of the
generic rigidity matroid and is proved to equal the same maximum realized rank.
The concrete operators use different coordinate and row-index types: this
repository uses functions `Fin d → ℝ` and an ordered-pair codomain, whereas
CombinatorialRigidity uses `EuclideanSpace ℝ (Fin d)` and the graph's edge
subtype.

The [rank-comparison package](../interop/combinatorial-rigidity/README.md) now
proves the exact comparison. Its coordinate equivalence `E = frameworkEquiv V d`
gives, for every placement `p`,

```text
BarJoint.rigidityRank G p = Module.finrank ℝ (G.RigidityMap (E p)).range
BarJoint.genericRigidityRank G d = G.genericRank d
```

The converted operators have identical kernels; rank--nullity proves equality
of their ranks. Maximum-rank attainment on both sides then proves the generic
identity. The statements require only `{V : Type} [Fintype V]` and allow every
`d : ℕ`, including empty vertex sets and zero dimension.

The package compiles the original `BarJoint.lean` source under Lean 4.34.0-rc2.
Its precise imports avoid the unrelated duplicate `Partition` definitions in
Mathlib and the Matroid dependency. The full body--pin proof remains checked
under Lean 4.29; it is not imported into this subproject.

The resulting predicate comparison is with
`G.genericRank d = (SimpleGraph.completeGraph V).genericRank d`.
Bryan's separate `IsGenericallyRigid` predicate has different small-vertex
semantics, so no unrestricted equivalence with that predicate is asserted.
