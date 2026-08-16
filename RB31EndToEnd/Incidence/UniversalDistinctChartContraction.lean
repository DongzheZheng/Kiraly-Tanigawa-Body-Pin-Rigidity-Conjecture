import RB31EndToEnd.Incidence.DistinctProvenanceChart
import RB31EndToEnd.Incidence.UniversalChartContraction

/-!
# Contracting a complete distinctness chart to pin provenance

This is the pairwise-distinct replacement for the earlier one-coordinate
contraction.  A chart denominator is the product of one labelled nonzero
twist-difference coordinate for every ordered pair of bodies.  The height
hypothesis is imposed only on homogeneous primes avoiding that product.
Thus equality components outside the intended incidence stratum do not enter
the obligation.

The abstract homogeneous-denominator theorem gives a power of the full
denominator in the generic chart ideal.  We undo the finite reindexing, clear
the pin-coefficient denominator, evaluate on a concrete distinct chart, and
descend from rational to integer coefficients.  No new height or properness
principle is asserted.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open NullCellulePolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Correct localized height interface -/

/-- Full-height requirement only for homogeneous primes meeting the chosen
pairwise-distinct provenance chart. -/
def FiniteGenericDistinctChartPrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
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
    finiteGenericDistinctnessDenominator (E := E) root distinctChart ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Reindexing and coefficient clearing for an arbitrary denominator -/

/-- Undo the finite twist-variable reindexing for an arbitrary polynomial,
not just a coordinate power. -/
theorem mem_genericUniversalChartIdeal_of_rename_mem_finite
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (f : GenericRelativeRing root E)
    (hmem :
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root)) f ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected) :
    f ∈ genericUniversalChartIdeal
      root src dst active angularChart selected := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  have hmapped :
      e.symm (e f) ∈
        Ideal.map e.symm.toRingEquiv.toRingHom
          (finiteGenericUniversalChartIdeal
            root src dst active angularChart selected) :=
    Ideal.mem_map_of_mem e.symm.toRingEquiv.toRingHom hmem
  rw [finiteGenericUniversalChartIdeal_eq_map_rename,
    Ideal.map_map] at hmapped
  have hcomp :
      e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
        RingHom.id (GenericRelativeRing root E) := by
    apply DFunLike.ext _ _
    intro g
    exact e.symm_apply_apply g
  rw [hcomp, Ideal.map_id] at hmapped
  simpa [e] using hmapped

/-- Generic coefficient extension of the complete distinctness denominator. -/
def genericDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (distinctChart : DistinctnessChart V) :
    GenericRelativeRing root E :=
  genericCoefficientExtensionHom root
    (universalDistinctnessDenominator (E := E) root distinctChart)

theorem finiteGenericDistinctnessDenominator_eq_rename_generic
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (distinctChart : DistinctnessChart V) :
    finiteGenericDistinctnessDenominator (E := E) root distinctChart =
      (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
        (finiteTwistIndexEquiv root))
        (genericDistinctnessDenominator (E := E) root distinctChart) := by
  rfl

/-- Coefficient-localization denominator clearing for an arbitrary source
polynomial. -/
theorem exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
    {A K σ : Type*} [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K]
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A)
    (hmem : algebraMap (MvPolynomial σ A) (MvPolynomial σ K) f ∈
      Ideal.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)) I) :
    ∃ q : A, q ≠ 0 ∧ C q * f ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := σ)))
    (MvPolynomial σ K)] at hmem
  obtain ⟨s, hs, hsmem⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hs
  exact ⟨q, nonZeroDivisors.ne_zero hq, hsmem⟩

/-! ## Localized contraction receipt -/

/-- The corrected distinct-chart height condition produces a rational pin
coefficient times a power of the complete provenance denominator in the
original universal chart ideal. -/
theorem exists_nonzero_pin_contraction_of_distinctChartPrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericDistinctChartPrimeHeightCondition
      root src dst active angularChart selected distinctChart) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q *
          universalDistinctnessDenominator (E := E) root distinctChart ^ m ∈
        universalChartIdeal
          root src dst active angularChart selected := by
  let s : FiniteGenericRelativeRing root E :=
    finiteGenericDistinctnessDenominator (E := E) root distinctChart
  have hsIrrelevant : s ∈
      finiteIrrelevantIdeal (k := GenericPinCoefficientField E)
        (groundedTwistVariableCount root) := by
    exact finiteGenericDistinctnessDenominator_mem_irrelevant
      (E := E) root distinctChart hTwo
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
          (genericDistinctnessDenominator (E := E) root distinctChart) ^ m ∈
        finiteGenericUniversalChartIdeal
          root src dst active angularChart selected := by
    simpa [s, finiteGenericDistinctnessDenominator_eq_rename_generic,
      map_pow] using hm
  have hmGeneric :
      genericDistinctnessDenominator (E := E) root distinctChart ^ m ∈
        genericUniversalChartIdeal
          root src dst active angularChart selected :=
    mem_genericUniversalChartIdeal_of_rename_mem_finite
      root src dst active angularChart selected _ (by
        simpa only [map_pow] using hmRenamed)
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E)
          (universalDistinctnessDenominator
            (E := E) root distinctChart ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal
            root src dst active angularChart selected) := by
    simpa [genericUniversalChartIdeal, genericDistinctnessDenominator,
      genericCoefficientExtensionHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_mem_of_mem_fraction_map
      (universalChartIdeal
        root src dst active angularChart selected)
      (universalDistinctnessDenominator (E := E) root distinctChart ^ m)
      hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Real evaluation and integer descent -/

/-- A distinct-chart contraction receipt forces its rational pin coefficient
to vanish at every actual realization in that provenance chart. -/
theorem eval_pinContraction_eq_zero_of_distinctIncidenceRealization
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (angularChart : active → Fin 3)
    (selected : Finset active) (distinctChart : DistinctnessChart V)
    (q : PinParameterRing E) (m : ℕ)
    (hmem : C q *
        universalDistinctnessDenominator (E := E) root distinctChart ^ m ∈
      universalChartIdeal root src dst active angularChart selected)
    (hdenom : realChartEvaluation root p Y
      (universalDistinctnessDenominator (E := E) root distinctChart) ≠ 0) :
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

/-- End-to-end integer certificate on one complete pairwise-distinct chart. -/
theorem exists_nonzero_integer_pin_certificate_of_distinctChartPrimeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hTwo : 2 ≤ Fintype.card V)
    (hheight : FiniteGenericDistinctChartPrimeHeightCondition
      root src dst active angularChart selected distinctChart) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        realChartEvaluation root p Y
          (universalDistinctnessDenominator (E := E) root distinctChart) ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ :=
    exists_nonzero_pin_contraction_of_distinctChartPrimeHeight
      root src dst active angularChart selected distinctChart hTwo hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hdenom
  apply hDescent (GroundedTwistPolynomial.assignmentOfPins p)
  exact eval_pinContraction_eq_zero_of_distinctIncidenceRealization
    hY root angularChart selected distinctChart q m hmem hdenom

end

end UniversalHomogeneousChart

end RB31E2E
