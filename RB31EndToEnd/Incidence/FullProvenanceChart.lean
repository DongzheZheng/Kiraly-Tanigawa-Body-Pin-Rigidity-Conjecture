import RB31EndToEnd.Incidence.DistinctProvenanceChart

/-!
# Complete incidence-provenance charts

Pairwise distinctness removes equality-collapse components, but the
private-pin triangular presentation also needs one nonzero angular
coordinate for every active occurrence.  This file records both pieces in
one denominator.  Its factors retain their body-pair and occurrence
provenance.

Every injective incidence realization belongs to one such finite chart.
After generic coefficient extension, the complete denominator lies in the
twist irrelevant ideal.  No height assertion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open NullCellulePolynomial

/-! ## The angular and complete denominators -/

/-- The angular-coordinate factor attached to one active occurrence. -/
def universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    RelativeRing root E :=
  universalBodyDifferenceCoordinate (E := E) root
    ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩
    ⟨false, angularChart e⟩

/-- Product of the selected nonzero angular coordinates of all active
relative twists. -/
def universalAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) : RelativeRing root E :=
  ∏ e : active,
    universalActiveAngularFactor root src dst active hLoop angularChart e

/-- The complete denominator: all labelled body differences and all
selected active angular coordinates. -/
def universalIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : RelativeRing root E :=
  universalDistinctnessDenominator (E := E) root distinctChart *
    universalAngularDenominator root src dst active hLoop angularChart

/-! ## Evaluation on the intended incidence locus -/

theorem realChartEvaluation_universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    realChartEvaluation root p Y
        (universalActiveAngularFactor
          root src dst active hLoop angularChart e) =
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) := by
  rw [universalActiveAngularFactor,
    realChartEvaluation_universalBodyDifferenceCoordinate]
  rfl

/-- The angular denominator is nonzero on the chosen angular chart. -/
theorem realChartEvaluation_universalAngularDenominator_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hAngular : ∀ e : active,
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) ≠ 0) :
    realChartEvaluation root p Y
        (universalAngularDenominator
          root src dst active hLoop angularChart) ≠ 0 := by
  rw [universalAngularDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun e _he ↦ by
    rw [realChartEvaluation_universalActiveAngularFactor]
    exact hAngular e

/-- Every injective incidence realization evaluates its complete
provenance denominator nontrivially on the charts supplied by its labelled
differences and active angular coordinates. -/
theorem realChartEvaluation_universalIncidenceProvenanceDenominator_ne_zero
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (hDistinct : ∀ uv : OrderedDistinctBodyPair V,
      twistCoordinates (Y uv.1.1 - Y uv.1.2) (distinctChart uv) ≠ 0)
    (hAngular : ∀ e : active,
      (Y (src e.1) - Y (dst e.1)).1 (angularChart e) ≠ 0) :
    realChartEvaluation root p Y
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) ≠ 0 := by
  rw [universalIncidenceProvenanceDenominator, map_mul]
  exact mul_ne_zero
    (realChartEvaluation_universalDistinctnessDenominator_ne_zero
      root distinctChart p Y hDistinct)
    (realChartEvaluation_universalAngularDenominator_ne_zero
      root src dst active hLoop angularChart p Y hAngular)

/-! ## The complete denominator in the finite generic chart -/

/-- Generic coefficient extension and finite twist reindexing of the
complete provenance denominator. -/
def finiteGenericIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    FiniteGenericRelativeRing root E :=
  finiteGenericChartHom root
    (universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart)

/-- With at least two bodies, the complete provenance denominator belongs
to the finite irrelevant ideal.  The pairwise-distinct factor already has
positive twist degree; multiplication by the angular factors preserves
ideal membership. -/
theorem finiteGenericIncidenceProvenanceDenominator_mem_irrelevant
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (hTwo : 2 ≤ Fintype.card V) :
    finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
  rw [finiteGenericIncidenceProvenanceDenominator,
    universalIncidenceProvenanceDenominator, map_mul]
  exact Ideal.mul_mem_right _ _
    (finiteGenericDistinctnessDenominator_mem_irrelevant
      (E := E) root distinctChart hTwo)

end

end UniversalHomogeneousChart

end RB31E2E
