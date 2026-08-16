import RB31EndToEnd.Algebra.FiniteChartCertificates
import RB31EndToEnd.Incidence.SkeletonOccurrenceSelection
import RB31EndToEnd.Incidence.UniversalFullProvenanceChartContraction

/-!
# Finite complete-provenance assembly of sparse-null properness

The finite chart index retains a grounding body, a complete pairwise-
distinct chart, and one active angular chart.  The corresponding denominator
contains every factor used by the localized height argument.  Chartwise
integer certificates are multiplied, and every injective incidence
realization selects a factor which vanishes on its pin placement.

The outer chart quantifiers remain explicit.  The innermost prime,
denominator-avoidance, and height quantifiers use the definition
`FiniteGenericIncidenceProvenancePrimeHeightCondition`.
-/

namespace RB31E2E

namespace SparseNullIncidence

noncomputable section

open MvPolynomial
open UniversalHomogeneousChart

/-! ## Fixed-data finite assembly -/

theorem exists_uniform_integer_pin_certificate_of_fullProvenancePrimeHeights
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (selected : Finset active)
    (hTwo : 2 ≤ Fintype.card V)
    (hHeight :
      ∀ (root : V) (distinctChart : DistinctnessChart V)
        (angularChart : active → Fin 3),
        FiniteGenericIncidenceProvenancePrimeHeightCondition
          root src dst active hLoop angularChart selected distinctChart) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        IsIncidenceRealization src dst active p Y →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  have hChartCertificate :
      ∀ i : Σ root : V,
          DistinctnessChart V × (active → Fin 3),
        ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
          Q ≠ 0 ∧
          ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
            IsIncidenceRealization src dst active p Y →
            realChartEvaluation i.1 p Y
                (universalIncidenceProvenanceDenominator
                  i.1 src dst active hLoop i.2.1 i.2.2) ≠ 0 →
            eval₂ (Int.castRingHom ℝ)
              (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
    intro i
    exact
      exists_nonzero_integer_pin_certificate_of_incidenceProvenancePrimeHeight
        i.1 src dst active hLoop i.2.2 selected i.2.1 hTwo
          (hHeight i.1 i.2.1 i.2.2)
  choose certificate hCertificateNonzero hCertificateVanish using
    hChartCertificate
  refine ⟨FiniteChartCertificates.combinedCertificate certificate,
    FiniteChartCertificates.combinedCertificate_ne_zero
      certificate hCertificateNonzero, ?_⟩
  intro p Y hY
  have hOne : 1 < Fintype.card V := by omega
  obtain ⟨root, _other, _hrootOther⟩ :=
    Fintype.one_lt_card_iff.mp hOne
  obtain ⟨distinctChart, hDistinctChart⟩ :=
    exists_distinctnessChart_of_injective Y hY.1
  obtain ⟨angularChart, hAngularChart, _hGeneration⟩ :=
    IsIncidenceRealization.exists_global_generation_chart hY hLoop
  let i : Σ root : V,
      DistinctnessChart V × (active → Fin 3) :=
    ⟨root, ⟨distinctChart, angularChart⟩⟩
  have hDenominator :
      realChartEvaluation i.1 p Y
          (universalIncidenceProvenanceDenominator
            i.1 src dst active hLoop i.2.1 i.2.2) ≠ 0 := by
    exact
      realChartEvaluation_universalIncidenceProvenanceDenominator_ne_zero
        i.1 src dst active hLoop i.2.1 i.2.2 p Y
          hDistinctChart hAngularChart
  exact FiniteChartCertificates.eval₂_combinedCertificate_eq_zero_of_chart
    certificate (GroundedTwistPolynomial.assignmentOfPins p) i
      (hCertificateVanish i p Y hY hDenominator)

/-! ## Assembly into the literal properness target -/

/-- Complete-provenance localized height, for every sparse-null input and
every finite chart, implies the literal `PropernessPrinciple` consumed by
the body--pin sufficiency proof. -/
theorem propernessPrinciple_of_finiteGenericFullProvenancePrimeHeights
    (hHeight :
      ∀ (V E : Type) [Fintype V] [DecidableEq V]
        [Fintype E] [DecidableEq E]
        (src dst : E → V) (active : Finset E)
        (hLoop : ∀ e ∈ active, src e ≠ dst e)
        (F : SimpleEdgeSet V)
        (_hTwo : 2 ≤ Fintype.card V)
        (_hSparse : Sparse22 F)
        (hRepresented : ∀ f ∈ F, ∃ e : active,
          activeEdge src dst active hLoop e = f)
        (_hcard : F.card =
          6 * (Fintype.card V - 1) - 2 * active.card),
        ∀ (root : V) (distinctChart : DistinctnessChart V)
          (angularChart : active → Fin 3),
          FiniteGenericIncidenceProvenancePrimeHeightCondition
            root src dst active hLoop angularChart
              (selectedSkeletonOccurrences
                src dst active hLoop F hRepresented)
              distinctChart) :
    PropernessPrinciple := by
  intro V E _instFV _instDV _instFE _instDE
    src dst active hLoop F hTwo hSparse hRepresented hcard
  let selected : Finset active :=
    selectedSkeletonOccurrences
      src dst active hLoop F hRepresented
  apply exists_uniform_integer_pin_certificate_of_fullProvenancePrimeHeights
    src dst active hLoop selected hTwo
  intro root distinctChart angularChart
  simpa [selected] using
    hHeight V E src dst active hLoop F hTwo hSparse
      hRepresented hcard root distinctChart angularChart

end

end SparseNullIncidence

/-! ## Reduction to localized prime heights -/

/-- The body--pin statement follows from the complete-provenance
localized-height condition.  Its innermost prime and
height quantifiers use the transparent definition
`FiniteGenericIncidenceProvenancePrimeHeightCondition`. -/
theorem endToEndBodyPinStatement_of_finiteGenericFullProvenancePrimeHeights
    (hHeight :
      ∀ (V E : Type) [Fintype V] [DecidableEq V]
        [Fintype E] [DecidableEq E]
        (src dst : E → V) (active : Finset E)
        (hLoop : ∀ e ∈ active, src e ≠ dst e)
        (F : SimpleEdgeSet V)
        (_hTwo : 2 ≤ Fintype.card V)
        (_hSparse : Sparse22 F)
        (hRepresented : ∀ f ∈ F, ∃ e : active,
          SparseNullIncidence.activeEdge
            src dst active hLoop e = f)
        (_hcard : F.card =
          6 * (Fintype.card V - 1) - 2 * active.card),
        ∀ (root : V)
          (distinctChart :
            UniversalHomogeneousChart.DistinctnessChart V)
          (angularChart : active → Fin 3),
          UniversalHomogeneousChart.FiniteGenericIncidenceProvenancePrimeHeightCondition
              root src dst active hLoop angularChart
                (SparseNullIncidence.selectedSkeletonOccurrences
                  src dst active hLoop F hRepresented)
                distinctChart) :
    EndToEndBodyPinStatement := by
  apply endToEndBodyPinStatement_of_sparseNullIncidenceProperness
  exact
    SparseNullIncidence.propernessPrinciple_of_finiteGenericFullProvenancePrimeHeights
      hHeight

end RB31E2E
