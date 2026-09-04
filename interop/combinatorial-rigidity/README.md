# Rigidity-rank comparison

This package proves that the two projects' real bar--joint rigidity ranks agree.
It imports Bryan Gin-ge Chen's `CombinatorialRigidity` and directly compiles
`../../RB31EndToEnd/Rigidity/BarJoint.lean`; no definitions are copied.

For a finite vertex type `V : Type`, a simple graph `G`, a dimension `d : ℕ`,
and a real placement `p`, let `E p` be the same coordinates regarded as a
Euclidean-space-valued framework. The proved identities are

```text
BarJoint.rigidityRank G p
  = Module.finrank ℝ (G.RigidityMap (E p)).range

BarJoint.genericRigidityRank G d = G.genericRank d
```

They hold for every placement, including coincident vertices, and for empty
vertex sets, zero dimension, and graphs without edges. The generic-rank
identity also gives

```text
BarJoint.IsGenericallyRigidInDimension G d ↔
  G.genericRank d = (SimpleGraph.completeGraph V).genericRank d
```

The coordinate conversion `frameworkEquiv` is a linear equivalence. The two
operators have the same kernel after this conversion, so rank--nullity gives
the first identity. The second follows because each definition of generic
rank bounds every realized rank and is attained by a placement.

## Proof modules

- `RB31BryanInterop.RealizedRank` defines the coordinate equivalence and proves
  `rigidityRank_eq_finrank_range`.
- `RB31BryanInterop.GenericRank` proves `genericRigidityRank_eq_genericRank` and
  `isGenericallyRigidInDimension_iff_genericRank_eq_complete`.
- `Tests/Trust.lean` exposes their types and axiom dependencies.

All three theorems are in the namespace `RB31E2E.BryanInterop`. Their proofs
contain no placeholders or added axioms and use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduce

From this directory, with elan installed:

```bash
lake exe cache get
./verify.sh
```

The checked-in toolchain and manifest pin Lean `4.34.0-rc2`,
CombinatorialRigidity `581c0112c91fddc125f6990ebe04256829839413`, and mathlib
`8b36e86753f10a65aad1d2b23a02df7d5bebc84a`, together with all transitive
dependencies. GitHub Actions checks this package separately from the main
Lean `4.29.0` development. Its build artifacts remain in this directory's
`.lake/`.

The full body--pin root theorem remains in the main development. This package
establishes the rank comparison and its maximum-rank predicate consequence;
it does not import that root theorem or formalize the Asimow--Roth bridge.
Bryan's separate `IsGenericallyRigid` predicate uses a bound on kernel
dimension, which differs from comparison with the complete graph for small
vertex sets. The predicate equivalence above therefore retains the
complete-graph rank explicitly.
