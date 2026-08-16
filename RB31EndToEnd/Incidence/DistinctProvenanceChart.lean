import RB31EndToEnd.Algebra.HomogeneousDenominatorContradiction
import RB31EndToEnd.Incidence.UniversalChartHeightElimination

/-!
# Finite provenance charts for the pairwise-distinct locus

A single nonzero grounded coordinate removes the common scaling orbit, but
it does not exclude components on which some other two body twists coincide.
The correct finite chart remembers one nonzero difference coordinate for
every ordered pair of distinct body labels.  Its denominator is the product
of those labelled linear forms.

This file defines that denominator and proves the two bookkeeping facts
needed by localized height elimination:

* every injective real twist assignment lies in one of the finite charts;
* after generic coefficient extension and finite reindexing, the denominator
  belongs to the twist irrelevant ideal (when there are at least two bodies).

No sparse-null height assertion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An ordered pair of genuinely distinct body labels.  Using ordered pairs
keeps endpoint provenance explicit and avoids an arbitrary orientation of
`Sym2`. -/
abbrev OrderedDistinctBodyPair (V : Type*) :=
  {uv : V × V // uv.1 ≠ uv.2}

/-- One of six nonzero relative-twist coordinates for every labelled
ordered pair. -/
abbrev DistinctnessChart (V : Type*) :=
  OrderedDistinctBodyPair V → TwistCoordinate

/-- One coordinate of the universal grounded twist at a body. -/
def universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) : RelativeRing root E :=
  if c.1 then
    (universalGroundedTwist (E := E) root v).2 c.2
  else
    (universalGroundedTwist (E := E) root v).1 c.2

/-- The provenance-labelled linear coordinate of `Y(u)-Y(v)`. -/
def universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    RelativeRing root E :=
  universalGroundedCoordinate (E := E) root uv.1.1 c -
    universalGroundedCoordinate (E := E) root uv.1.2 c

/-- Product cutting out the complement of one complete pairwise-distinct
provenance chart. -/
def universalDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) : RelativeRing root E :=
  ∏ uv : OrderedDistinctBodyPair V,
    universalBodyDifferenceCoordinate (E := E) root uv (chart uv)

/-- A universal grounded coordinate specializes to the corresponding
coordinate of `Y(v)-Y(root)`. -/
theorem realChartEvaluation_universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalGroundedCoordinate (E := E) root v c) =
      twistCoordinates (Y v - Y root) c := by
  rcases c with ⟨b, i⟩
  cases b
  · have h := congrFun
      (congrArg Prod.fst
        (map_universalGroundedTwist root v p Y)) i
    simpa [universalGroundedCoordinate, mapTwist, mapVec3] using h
  · have h := congrFun
      (congrArg Prod.snd
        (map_universalGroundedTwist root v p Y)) i
    simpa [universalGroundedCoordinate, mapTwist, mapVec3] using h

/-- Difference-coordinate evaluation is independent of the arbitrary
grounding body. -/
theorem realChartEvaluation_universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalBodyDifferenceCoordinate (E := E) root uv c) =
      twistCoordinates (Y uv.1.1 - Y uv.1.2) c := by
  rw [universalBodyDifferenceCoordinate, map_sub,
    realChartEvaluation_universalGroundedCoordinate,
    realChartEvaluation_universalGroundedCoordinate]
  rcases c with ⟨b, i⟩
  cases b <;> simp [twistCoordinates]

/-- Injectivity supplies a simultaneous finite distinctness chart. -/
theorem exists_distinctnessChart_of_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (Y : V → Twist ℝ) (hY : Function.Injective Y) :
    ∃ chart : DistinctnessChart V,
      ∀ uv : OrderedDistinctBodyPair V,
        twistCoordinates (Y uv.1.1 - Y uv.1.2) (chart uv) ≠ 0 := by
  have hCoordinate : ∀ uv : OrderedDistinctBodyPair V,
      ∃ c : TwistCoordinate,
        twistCoordinates (Y uv.1.1 - Y uv.1.2) c ≠ 0 := by
    intro uv
    apply SparseNullIncidence.exists_twistCoordinate_ne_zero
    exact sub_ne_zero.mpr (hY.ne uv.2)
  choose chart hchart using hCoordinate
  exact ⟨chart, hchart⟩

/-- On its chosen chart, the complete provenance denominator evaluates to a
nonzero real number. -/
theorem realChartEvaluation_universalDistinctnessDenominator_ne_zero
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hchart : ∀ uv : OrderedDistinctBodyPair V,
      twistCoordinates (Y uv.1.1 - Y uv.1.2) (chart uv) ≠ 0) :
    realChartEvaluation root p Y
        (universalDistinctnessDenominator (E := E) root chart) ≠ 0 := by
  rw [universalDistinctnessDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun uv _huv ↦ by
    rw [realChartEvaluation_universalBodyDifferenceCoordinate]
    exact hchart uv

/-! ## Generic finite-ring denominator -/

/-- The same denominator after extending pin coefficients to their fraction
field and reindexing all grounded twist variables by a finite type. -/
def finiteGenericDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    FiniteGenericRelativeRing root E :=
  finiteGenericChartHom root
    (universalDistinctnessDenominator (E := E) root chart)

/-- Each grounded coordinate maps into the finite irrelevant ideal. -/
theorem finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root v : V) (c : TwistCoordinate) :
    finiteGenericChartHom (E := E) root
        (universalGroundedCoordinate (E := E) root v c) ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rcases c with ⟨b, i⟩
  cases b <;> by_cases hv : v = root
  · subst v
    simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot]
  · simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot, hv, universalOffRootTwist, finiteIrrelevantIdeal,
      X_mem_coordinateVariableIdeal_iff]
  · subst v
    simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot]
  · simp [universalGroundedCoordinate, universalGroundedTwist,
      extendOffRoot, hv, universalOffRootTwist, finiteIrrelevantIdeal,
      X_mem_coordinateVariableIdeal_iff]

/-- Every labelled pair-difference factor maps into the twist irrelevant
ideal. -/
theorem finiteGenericChartHom_universalBodyDifferenceCoordinate_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    finiteGenericChartHom (E := E) root
        (universalBodyDifferenceCoordinate (E := E) root uv c) ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rw [universalBodyDifferenceCoordinate, map_sub]
  exact Ideal.sub_mem _
    (finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
      (E := E) root uv.1.1 c)
    (finiteGenericChartHom_universalGroundedCoordinate_mem_irrelevant
      (E := E) root uv.1.2 c)

/-- With at least two bodies, the full generic distinctness denominator is
a positive-twist-degree element of the finite irrelevant ideal. -/
theorem finiteGenericDistinctnessDenominator_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V) :
    finiteGenericDistinctnessDenominator (E := E) root chart ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  have hOne : 1 < Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp hOne
  let uv : OrderedDistinctBodyPair V := ⟨(u, v), huv⟩
  let s : Finset (OrderedDistinctBodyPair V) := Finset.univ
  let f : OrderedDistinctBodyPair V → FiniteGenericRelativeRing root E :=
    fun w ↦ finiteGenericChartHom (E := E) root
      (universalBodyDifferenceCoordinate (E := E) root w (chart w))
  have huvMem : uv ∈ s := Finset.mem_univ uv
  have hfactor : f uv ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) :=
    finiteGenericChartHom_universalBodyDifferenceCoordinate_mem_irrelevant
      (E := E) root uv (chart uv)
  have hproduct :
      f uv * ∏ w ∈ s.erase uv, f w ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) :=
    Ideal.mul_mem_right _ _ hfactor
  rw [Finset.mul_prod_erase s f huvMem] at hproduct
  rw [finiteGenericDistinctnessDenominator,
    universalDistinctnessDenominator, map_prod]
  simpa [s, f] using hproduct

end

end UniversalHomogeneousChart

end RB31E2E
