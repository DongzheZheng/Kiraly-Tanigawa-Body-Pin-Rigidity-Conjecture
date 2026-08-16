import RB31EndToEnd.Incidence.UniversalChartHeightElimination
import RB31EndToEnd.Algebra.RationalCertificateDescent
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Contracting a generic universal chart to pin parameters

The height argument over the fraction field of the pin-parameter ring forces
a power of the selected twist coordinate into the generic chart ideal.  This
file transports that membership back through the finite variable reindexing
and then uses the actual localization theorem for multivariate polynomial
rings to clear the pin denominator.  The result is a provenance-retaining
receipt

`C q * X c ^ m ∈ universalChartIdeal`

with a nonzero rational pin polynomial `q`.  On a real chart where the twist
coordinate `c` is nonzero, semantic annihilation of the universal chart ideal
therefore forces `q` to vanish.  The final theorem applies
`RationalCertificateDescent` and returns a nonzero integer pin polynomial.

No new properness, height, elimination, or incidence proposition is assumed
in this file.  Its only geometric input is the already explicit
`FiniteGenericChartPrimeHeightCondition`.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## Clearing coefficients in a polynomial localization -/

/-- A denominator-clearing lemma specialized to coefficient localization.
Membership of a coordinate power after localizing the coefficient ring
produces one nonzero coefficient `q` whose constant embedding times that
power already belongs to the source ideal. -/
theorem exists_nonzero_coefficient_mul_X_pow_mem_of_mem_fraction_map
    {A K σ : Type*} [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K]
    (I : Ideal (MvPolynomial σ A)) (c : σ) (m : ℕ)
    (hmem : algebraMap (MvPolynomial σ A) (MvPolynomial σ K) (X c ^ m) ∈
      Ideal.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)) I) :
    ∃ q : A, q ≠ 0 ∧ C q * X c ^ m ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := σ)))
    (MvPolynomial σ K)] at hmem
  obtain ⟨s, hs, hsmem⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hs
  exact ⟨q, nonZeroDivisors.ne_zero hq, hsmem⟩

/-! ## Undoing the finite reindexing -/

/-- The un-reindexed generic relative ring. -/
abbrev GenericRelativeRing
    {V : Type*} [DecidableEq V] (root : V) (E : Type*) :=
  MvPolynomial (GroundedTwistVariable root)
    (GenericPinCoefficientField E)

/-- Coefficient extension without changing the twist provenance labels. -/
def genericCoefficientExtensionHom
    {V E : Type*} [DecidableEq V] (root : V) :
    RelativeRing root E →+* GenericRelativeRing root E :=
  MvPolynomial.map (genericPinCoefficientHom E)

/-- The universal chart ideal after extending only its pin coefficients. -/
def genericUniversalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Ideal (GenericRelativeRing root E) :=
  Ideal.map (genericCoefficientExtensionHom root)
    (universalChartIdeal root src dst active chart selected)

/-- The finite generic ideal is exactly the variable-renaming image of the
un-reindexed generic ideal. -/
theorem finiteGenericUniversalChartIdeal_eq_map_rename
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    finiteGenericUniversalChartIdeal root src dst active chart selected =
      Ideal.map
        (MvPolynomial.renameEquiv (GenericPinCoefficientField E)
          (finiteTwistIndexEquiv root)).toRingEquiv.toRingHom
        (genericUniversalChartIdeal
          root src dst active chart selected) := by
  rw [finiteGenericUniversalChartIdeal, genericUniversalChartIdeal,
    Ideal.map_map]
  rfl

/-- Undoing the finite reindexing transports a selected coordinate power
from the finite generic ideal to the coefficient-extended ideal with its
original provenance label. -/
theorem X_pow_mem_genericUniversalChartIdeal_of_mem_finite
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) (m : ℕ)
    (hmem : X (finiteTwistIndexEquiv root c) ^ m ∈
      finiteGenericUniversalChartIdeal
        root src dst active chart selected) :
    X c ^ m ∈ genericUniversalChartIdeal
      root src dst active chart selected := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  have hmapped :
      e.symm (X (finiteTwistIndexEquiv root c) ^ m) ∈
        Ideal.map e.symm.toRingEquiv.toRingHom
          (finiteGenericUniversalChartIdeal
            root src dst active chart selected) :=
    Ideal.mem_map_of_mem e.symm.toRingEquiv.toRingHom hmem
  rw [finiteGenericUniversalChartIdeal_eq_map_rename,
    Ideal.map_map] at hmapped
  have hcomp :
      e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
        RingHom.id (GenericRelativeRing root E) := by
    apply DFunLike.ext _ _
    intro f
    exact e.symm_apply_apply f
  rw [hcomp, Ideal.map_id] at hmapped
  simpa [e] using hmapped

/-! ## The rational contraction witness -/

/-- The prime-height input produces a genuine denominator-clearing receipt
in the original universal chart ideal.  The coefficient `q` is a nonzero
rational polynomial in the pin parameters alone. -/
theorem exists_nonzero_pin_contraction_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ (q : PinParameterRing E) (m : ℕ),
      q ≠ 0 ∧
      C q * X c ^ m ∈
        universalChartIdeal root src dst active chart selected := by
  obtain ⟨m, hm⟩ :=
    NullCellulePolynomial.exists_X_pow_mem_of_homogeneousPrime_height
      (finiteGenericUniversalChartIdeal
        root src dst active chart selected)
      (finiteGenericUniversalChartIdeal_isHomogeneous
        root src dst active chart selected)
      (finiteTwistIndexEquiv root c) hheight
  have hmGeneric : X c ^ m ∈ genericUniversalChartIdeal
      root src dst active chart selected :=
    X_pow_mem_genericUniversalChartIdeal_of_mem_finite
      root src dst active chart selected c m hm
  have hmLocalization :
      algebraMap (RelativeRing root E) (GenericRelativeRing root E) (X c ^ m) ∈
        Ideal.map
          (algebraMap (RelativeRing root E) (GenericRelativeRing root E))
          (universalChartIdeal root src dst active chart selected) := by
    simpa [genericUniversalChartIdeal, genericCoefficientExtensionHom] using hmGeneric
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coefficient_mul_X_pow_mem_of_mem_fraction_map
      (universalChartIdeal root src dst active chart selected) c m hmLocalization
  exact ⟨q, m, hq, hqmem⟩

/-! ## Evaluation and integer descent -/

/-- A denominator-clearing receipt forces its pin coefficient to vanish at
every actual incidence realization lying in the selected nonzero twist
chart. -/
theorem eval_pinContraction_eq_zero_of_incidenceRealization
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) (q : PinParameterRing E) (m : ℕ)
    (hmem : C q * X c ^ m ∈
      universalChartIdeal root src dst active chart selected)
    (hc : GroundedTwistPolynomial.twistCoordinates
      (Y c.1.1 - Y root) c.2 ≠ 0) :
    eval₂ (Rat.castHom ℝ) (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  have hzero :=
    IsIncidenceRealization.realChartEvaluation_annihilates_universalChartIdeal
      hY root chart selected hmem
  rw [RingHom.mem_ker, map_mul] at hzero
  have hCoeff : realChartEvaluation root p Y (C q) =
      pinParameterEvaluation p q := by
    simp [realChartEvaluation]
  rw [hCoeff, map_pow, realChartEvaluation_X] at hzero
  have hqzero : pinParameterEvaluation p q = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero m hc)
  simpa [pinParameterEvaluation] using hqzero

/-- A nonzero rational pin polynomial vanishes on every actual realization
in the selected chart. -/
theorem exists_nonzero_rational_pin_certificate_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ q : PinParameterRing E,
      q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        GroundedTwistPolynomial.twistCoordinates
          (Y c.1.1 - Y root) c.2 ≠ 0 →
        eval₂ (Rat.castHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) q = 0 := by
  obtain ⟨q, m, hq, hmem⟩ := exists_nonzero_pin_contraction_of_primeHeight
    root src dst active chart selected c hheight
  refine ⟨q, hq, ?_⟩
  intro p Y hY hc
  exact eval_pinContraction_eq_zero_of_incidenceRealization
    hY root chart selected c q m hmem hc

/-- End-to-end chart certificate: the height condition yields a nonzero
integer polynomial in the original pin-provenance variables, and every real
incidence realization in the selected nonzero twist chart annihilates it. -/
theorem exists_nonzero_integer_pin_certificate_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        SparseNullIncidence.IsIncidenceRealization src dst active p Y →
        GroundedTwistPolynomial.twistCoordinates
          (Y c.1.1 - Y root) c.2 ≠ 0 →
        eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  obtain ⟨q, hq, hqVanish⟩ :=
    exists_nonzero_rational_pin_certificate_of_primeHeight
      root src dst active chart selected c hheight
  obtain ⟨Q, _a, hQ, _ha, _hProportional, hDescent⟩ :=
    RationalCertificateDescent.exists_integer_certificate_vanishing_on_real_zeros
      q hq
  refine ⟨Q, hQ, ?_⟩
  intro p Y hY hc
  exact hDescent (GroundedTwistPolynomial.assignmentOfPins p)
    (hqVanish p Y hY hc)

end

end UniversalHomogeneousChart

end RB31E2E
