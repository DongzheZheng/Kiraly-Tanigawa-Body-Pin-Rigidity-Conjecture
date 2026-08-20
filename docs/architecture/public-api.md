# Public API contract

This document defines the supported Lean surface for the compatibility-first
library branch.  Only declarations in the exhaustive whitelist below are
public.  Facade module prose describes subject matter but does not turn every
transitively visible declaration into a compatibility promise.

## Import policy

Use the smallest facade that supplies the required semantics:

```lean
import RB31EndToEnd.API.BodyPin
import RB31EndToEnd.API.BodyTwist
```

The light aggregate is:

```lean
import RB31EndToEnd.API
```

It intentionally excludes the unconditional end-to-end proof.  Import the
capstone explicitly only when its theorem is needed:

```lean
import RB31EndToEnd.API.Theorem
```

The legacy entry point remains supported:

```lean
import RB31EndToEnd
```

but it loads the complete proof engine and should not be used as a foundation
for new Whiteley/Dress modules.

## Stability levels

- **Stable:** module path and declaration type are intended to remain source
  compatible through the next minor versions.
- **Experimental:** useful today, but may be replaced by a theorem-level
  compiler or a more abstract carrier.
- **Internal:** accessible Lean implementation detail with no compatibility
  promise.

All names below remain in the existing `RB31E2E` namespace in this phase.

## Exhaustive stable whitelist

The declarations below are the complete phase-one compatibility promise.
Imports expose additional names because Lean imports are transitive, but those
names are experimental or internal unless added to this list in a later
version.  This narrow whitelist is intentional: it leaves room to split and
move the current proof engine without freezing hundreds of implementation
lemmas.

Exact consumer-facing types are compiled independently in `Tests/API/`; every
such file imports one facade and no other project facade.

### `RB31EndToEnd.API.Graph`

- `LooplessMultiGraph`
- its record-construction contract with carrier projections `Vertex`, `Edge`,
  endpoint projections `source`, `target`, proof `loopless`, and the
  `Fintype`/`DecidableEq` fields and instances for both carriers
- `LooplessMultiGraph.HasEndpoints` and `hasEndpoints_comm`
- `LooplessMultiGraph.edgesBetween`, `edgesBetween_comm`, and
  `edgesBetween_self`
- `LooplessMultiGraph.multiplicity`
- `LooplessMultiGraph.multiplicity_comm` and `multiplicity_self`
- `LooplessMultiGraph.no_edge_has_equal_endpoints`
- `LooplessMultiGraph.underlyingSimpleGraph`
- `LooplessMultiGraph.underlyingSimpleGraph_adj_iff`
- `LooplessMultiGraph.underlyingSimpleGraph_adj_iff_multiplicity_pos`

The locked theorem shape is:

```lean
(G : LooplessMultiGraph) → (v w : G.Vertex) →
  G.multiplicity v w = G.multiplicity w v
```

### `RB31EndToEnd.API.Sparse22`

- `SimpleEdge V := {e : Sym2 V // ¬ e.IsDiag}`
- `SimpleEdgeSet V := Finset (SimpleEdge V)`
- `SimpleEdge.vertices : SimpleEdge V → Finset V`
- `edgesInside : SimpleEdgeSet V → Finset V → SimpleEdgeSet V`
- `Sparse22 : SimpleEdgeSet V → Prop`
- `Tight22 : SimpleEdgeSet V → Finset V → Prop`
- `sparse22_empty : Sparse22 (∅ : SimpleEdgeSet V)`
- `tight22_union_inter`
- `sparsePartitionTerm` and `exists_sparse22_of_all_partition_terms`
- `exists_tight22_completion`
- `Sparse22Transport.mapSimpleEdge`, `Sparse22Transport.mapEdgeSet`, and
  `Sparse22Transport.sparse22_of_mapEdgeSet_subset`

`SimpleEdge.vertices`, `edgesInside`, `Sparse22`, and `Tight22` retain their
`[DecidableEq V]` requirement; the two carrier abbreviations do not require an
instance.  Nixon--Owen construction predicates, degree-three reductions, and
graph-extension witness structures remain experimental.

### `RB31EndToEnd.API.Linear`

- `FiniteFamilyBaseChange.mapVector`
- `FiniteFamilyBaseChange.finrank_span_range_mapVector`
- `FiniteFamilyBaseChange.finrank_span_range_mapVector_finite`
- `FiniteRowSystem.matrix`, `constraint`, `synthesis`, and `stressDim`
- `FiniteRowSystem.finrank_range_constraint_eq_finrank_range_synthesis`
- `FiniteRowSystem.solutionDim_add_rowCard_eq_coordinateCard_add_stressDim`
- `FiniteRowSystem.finrank_span_add_stressDim_eq_card`
- `BlockKernelExact.blockMap`, `connectingMap`, and `finrank_blockKernel`

For finite coordinate and row types over a field, the locked identity is:

```lean
Module.finrank k (LinearMap.ker (FiniteRowSystem.constraint row)) +
    Fintype.card J =
  Fintype.card I + FiniteRowSystem.stressDim row
```

The auxiliary lift maps used inside the block-kernel proof remain
experimental; only the two maps and final dimension identity named above are
stable.

### `RB31EndToEnd.API.Algebra`

- `AffineSpanDescent.affineCoefficients_mem_span`
- `CoordinateFieldTower.oldCoordinateField`
- `CoordinateFieldTower.trdeg_deletion_ledger`
- `ComplexRealSpecialization.exists_real_eval_ne_zero`
- `ComplexRealSpecialization.specializeMatrix`
- `ComplexRealSpecialization.exists_real_specialization_injective_of_complex`
- `FiniteChartCertificates.exists_uniform_certificate_of_finite_chart_cover`
- `FractionQuotientCoordinates.coordinate`
- `FractionQuotientCoordinates.adjoin_coordinate_eq_top`
- `RationalCertificateDescent.exists_integer_product_certificate`

Its locked shape is:

```lean
(P : MvPolynomial σ ℝ) → P ≠ 0 →
  ∃ x : σ → ℝ, MvPolynomial.eval x P ≠ 0
```

Universal chart layouts, denominator choices, pin-specific prime-height
transfers, and NullCellule replacement tables are internal.

### `RB31EndToEnd.API.BarJoint`

- `BarJoint.Point d := Fin d → ℝ`
- `BarJoint.Placement V d := V → Fin d → ℝ`
- `BarJoint.Velocity V d := V → Fin d → ℝ`
- `BarJoint.edgeConstraint` and `edgeFunctional`
- `BarJoint.rigidityOperator`
- `BarJoint.IsInfinitesimalMotion`
- `BarJoint.rigidityRank` and `RankIsAttained`
- `BarJoint.genericRigidityRank`
- `BarJoint.exists_rigidityRank_eq_genericRigidityRank`
- `BarJoint.IsGenericallyRigidInDimension`
- `BarJoint.IsGenericallyRigidInR3`
- `BarJoint.completeFrameworkRankTarget`

The two principal locked result types are:

```lean
BarJoint.rigidityOperator G p :
  BarJoint.Velocity V d →ₗ[ℝ] (V × V → ℝ)

BarJoint.genericRigidityRank G d : ℕ
```

The equality between the generic rank of every complete framework and
`completeFrameworkRankTarget` is not yet a public theorem; consumers must not
assume it from the numerical target's name.

### `RB31EndToEnd.API.BodyPin`

- `pinCapacity : ℕ → ℕ`
- `BodyPinIncidence`
- its record-construction contract with carrier projections `Body`, `Pin`,
  endpoint projections `left`, `right`, proof `loopless`, and the
  `Fintype`/`DecidableEq` fields and instances for both carriers
- `BodyPinIncidence.partitionCapacity`
- `BodyPinIncidence.PartitionCondition`
- `BodyPinIncidence.FinpartitionCondition`
- `BodyPinIncidence.finpartitionCapacity`
- `BodyPinIncidence.partitionCondition_iff_finpartitionCondition`
- `BodyPinIncidence.BPVertex`
- `BodyPinIncidence.bodyPinGraph`
- `BodyPinIncidence.canonicalBodyPinGraph`
- `BodyPinIncidence.GenericallyRigidInR3`
- `BarJoint.completeFrameworkRankTarget`
- `completeFrameworkRankTarget_three_add_pinCapacity`
- `pinCapacity_add_completeFrameworkRankTarget_three`
- `sum_completeFrameworkRankTarget_three_add_sum_pinCapacity`

The scalar bridge is locked as:

```lean
(m : ℕ) →
  BarJoint.completeFrameworkRankTarget 3 m + pinCapacity m = 3 * m
```

The three arithmetic theorems are defined in the ordinary reusable provider
`RB31EndToEnd.Rigidity.BodyPinRankAccounting`; the facade only aggregates it.
Other unlisted incidence, finite-partition, and expanded-graph declarations
remain experimental until exercised by a real downstream abstraction.

### `RB31EndToEnd.API.BodyTwist`

- `Vec3 k := Fin 3 → k`
- `Vec3.dot` and `Vec3.cross`
- `Twist k := Vec3 k × Vec3 k`
- `Twist.eval`, `Twist.splitKlein`, and `Twist.CompatibleAt`
- `IsTwistMotion`, `IsDiagonalTwist`, `TwistRigidAt`, and
  `HasRigidTwistRealization`
- `Twist.evalLinear` and `Twist.twoPinLinear`
- `Twist.finrank_range_evalLinear_le_three`
- `Twist.finrank_range_twoPinLinear_le_five`
- `Twist.bundleLinear`
- `Twist.finrank_range_bundleLinear_le_pinCapacity`

The rank bound is locked as:

```lean
Module.finrank k (LinearMap.range (Twist.bundleLinear p)) ≤ pinCapacity m
```

The body-twist/bar-joint bridge theorems, including
`BodyPinIncidence.genericallyRigidInR3_of_twistRigidAt`, are exposed for current
experiments but are not in the stable whitelist.  Their carrier shape and
adjacent machinery may be replaced by a smaller compiler interface.

### `RB31EndToEnd.API.Theorem`

- `EndToEndBodyPinStatement`
- `endToEndBodyPinStatement : EndToEndBodyPinStatement`
- `BodyPinIncidence.genericallyRigidInR3_iff_partitionCondition`

The direct endpoint is locked as:

```lean
(H : BodyPinIncidence) → (extra : H.Body → ℕ) →
  H.GenericallyRigidInR3 extra ↔ H.PartitionCondition
```

The public statement is unconditional in Lean and retains the existing trust
boundary.  Its provenance-flag, chart, prime-height, and null-cellule route is
internal.

## Whiteley/Dress extension boundary

New target modules should build on the graph, linear, algebra, and bar--joint
facades.  Before either conjecture is stated in the library, the following
rank-valued semantic layer is required:

1. rigidity rank on arbitrary finite edge sets;
2. a finite rank-system/matroid interface and closure;
3. the `C_2^1` cofactor rank system;
4. maximal clique, hinge, and clique-cover data;
5. bridges from the current maximum-real-rank definitions to those objects.

The BodyPin theorem is the first target adapter and a source of reusable
mechanisms.  It is not itself the definition of the Whiteley or Dress target.
