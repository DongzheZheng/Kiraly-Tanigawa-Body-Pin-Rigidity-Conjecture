import RB31EndToEnd.Incidence.FullProvenanceChart
import RB31EndToEnd.Incidence.UniversalDistinctChartContraction

/-!
# Contraction on the complete incidence-provenance chart

The complete chart denominator records both sources of localization used by
the proof: pairwise body distinctness and one nonzero angular coordinate for
every active occurrence.  A full-height theorem only on primes avoiding this
product suffices to eliminate the grounded twist variables and produce a
nonzero polynomial in the original pin parameters.

This file is denominator elimination and evaluation bookkeeping.  It does
not assert the localized prime-height theorem.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The exact localized-height interface -/

/-- Full twist height is required only for homogeneous primes which meet
the complete pairwise-distinct and active-angular chart. -/
def FiniteGenericIncidenceProvenancePrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : Prop :=
  ∀ (Q : Ideal (FiniteGenericRelativeRing root E)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) →
    finiteGenericUniversalChartIdeal
      root src dst active angularChart selected ≤ Q →
    finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Generic reindexing of the complete denominator -/

def genericIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : GenericRelativeRing root E :=
  genericCoefficientExtensionHom root
    (universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart)

theorem finiteGenericIncidenceProvenanceDenominator_eq_rename_generic
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart =
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root))
        (genericIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) := by
  rfl

/-! ## Elimination to the pin ring -/

/-- The complete localized-height condition yields a rational pin
coefficient times a power of the complete provenance denominator in the
original universal chart ideal. -/
theorem exists_nonzero_pin_contraction_of_incidenceProvenancePrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q *
          universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart ^ m ∈
        universalChartIdeal
          root src dst active angularChart selected := by
  let s : FiniteGenericRelativeRing root E :=
    finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart
  have hsIrrelevant : s ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
    exact finiteGenericIncidenceProvenanceDenominator_mem_irrelevant
      root src dst active hLoop distinctChart angularChart hTwo
  obtain ⟨m, hm⟩ :=
    exists_denominator_pow_mem_of_homogeneousPrime_height
      (finiteGenericUniversalChartIdeal
        root src dst active angularChart selected)
      (finiteGenericUniversalChartIdeal_isHomogeneous
        root src dst active angularChart selected)
      s hsIrrelevant hheight
  have hmRenamed :
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
          (finiteTwistIndexEquiv root))
          (genericIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart) ^ m ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected := by
    simpa [s,
      finiteGenericIncidenceProvenanceDenominator_eq_rename_generic,
      map_pow] using hm
  have hmGeneric :
      genericIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart ^ m ∈
        genericUniversalChartIdeal
          root src dst active angularChart selected :=
    mem_genericUniversalChartIdeal_of_rename_mem_finite
      root src dst active angularChart selected _ (by
        simpa only [map_pow] using hmRenamed)
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E)
          (universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal
            root src dst active angularChart selected) := by
    simpa [genericUniversalChartIdeal,
      genericIncidenceProvenanceDenominator,
      genericCoefficientExtensionHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
      (universalChartIdeal
        root src dst active angularChart selected)
      (universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ^ m)
      hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Evaluation and integer descent -/

theorem eval_pinContraction_eq_zero_of_incidenceProvenanceRealization
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (q : PinParameterRing E) (m : ℕ)
    (hmem : C q *
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart ^ m ∈
      universalChartIdeal root src dst active angularChart selected)
    (hdenom : realChartEvaluation root p Y
      (universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart) ≠ 0) :
    eval₂ (Rat.castHom ℝ)
      (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  have hzero :=
    IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
      hY root angularChart selected hmem
  rw [RingHom.mem_ker, map_mul] at hzero
  have hCoeff : realChartEvaluation root p Y (C q) =
      pinParameterEvaluation p q := by
    simp [realChartEvaluation]
  rw [hCoeff, map_pow] at hzero
  have hqzero : pinParameterEvaluation p q = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero m hdenom)
  simpa [pinParameterEvaluation] using hqzero

/-- End-to-end integer pin certificate on one complete incidence chart. -/
theorem exists_nonzero_integer_pin_certificate_of_incidenceProvenancePrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        realChartEvaluation root p Y
          (universalIncidenceProvenanceDenominator
            root src dst active hLoop distinctChart angularChart) ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ :=
    exists_nonzero_pin_contraction_of_incidenceProvenancePrimeHeight
      root src dst active hLoop angularChart selected distinctChart
        hTwo hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hdenom
  apply hDescent (GroundedTwistPolynomial.assignmentOfPins p)
  exact eval_pinContraction_eq_zero_of_incidenceProvenanceRealization
    hY root hLoop angularChart selected distinctChart q m hmem hdenom

end

end UniversalHomogeneousChart

end RB31E2E
