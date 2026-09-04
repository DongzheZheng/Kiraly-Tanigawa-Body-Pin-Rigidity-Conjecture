# Interoperability with CombinatorialRigidity

This repository and Bryan Gin-ge Chen's
[CombinatorialRigidity](https://github.com/bryangingechen/CombinatorialRigidity)
use the same graph-theoretic separation:

- a body-level multigraph has an independent type of edge occurrences;
- an expanded bar--joint framework is a mathlib `SimpleGraph`.

The compatibility surface was designed against the public API in
CombinatorialRigidity commit
`581c0112c91fddc125f6990ebe04256829839413`. The two packages are not yet
compiled as a single dependency graph.

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
subtype. A cross-project theorem therefore requires an equal-rank comparison,
using the coordinate-space equivalence together with restriction and extension
between the two row-index spaces.

That rank bridge is kept outside the present dependency closure. This release
uses Lean 4.29.0, while the checked CombinatorialRigidity revision uses Lean
4.34.0-rc2 and an additional Matroid dependency. A direct package dependency
would consequently require a coordinated toolchain migration. The conceptual
separation between the `Graph` and `SimpleGraph` layers is already shared; its
Lean API must be rechecked as part of that migration.
