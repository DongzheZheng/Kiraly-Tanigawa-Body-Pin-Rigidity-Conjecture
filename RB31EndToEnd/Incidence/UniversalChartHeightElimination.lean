import RB31EndToEnd.Incidence.UniversalChartIdeal
import RB31EndToEnd.Algebra.HomogeneousChartContradiction
import RB31EndToEnd.Incidence.Arithmetic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Height elimination for a universal incidence chart

The outer polynomial ring of `UniversalChartIdeal` has the pin-parameter
ring as coefficients.  Since the homogeneous height theorem used here is a
theorem over a field, this file performs the two honest changes of
coordinates required to apply it:

* extend the pin coefficients to their fraction field; and
* reindex the finite type of grounded twist variables by `Fin n`.

The image of the universal chart ideal under this composite map remains
standard homogeneous.  Under an explicitly named lower-height condition on
the homogeneous primes over that finite generic ideal, the existing
`map_eq_top_of_homogeneousPrime_height` theorem shows that every algebra map
which makes a selected twist coordinate a unit sends the ideal to `top`.
The final theorem is stated back on the original universal chart ideal via
the composite ring homomorphism.

No incidence height estimate is asserted in this file: the precise missing
estimate is exposed as `FiniteGenericChartPrimeHeightCondition`.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Generic coefficients and finite twist coordinates -/

/-- The generic coefficient field obtained from the provenance-labelled pin
parameter ring. -/
abbrev GenericPinCoefficientField (E : Type*) :=
  FractionRing (PinParameterRing E)

/-- The actual number of outer, grounded-twist variables. -/
def groundedTwistVariableCount {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) : ℕ :=
  Fintype.card (GroundedTwistVariable root)

/-- There are exactly six twist coordinates for every body other than the
grounded root. -/
theorem groundedTwistVariableCount_eq_six_mul_pred
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) :
    groundedTwistVariableCount root = 6 * (Fintype.card V - 1) := by
  have hoff : Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V ↦ v = root)]
    simp
  simp [groundedTwistVariableCount, GroundedTwistVariable,
    GroundedTwistPolynomial.GroundedColumn,
    GroundedTwistPolynomial.TwistCoordinate, hoff, Nat.mul_comm]

/-- The two-coordinate provenance index has exactly two entries for each
active occurrence. -/
theorem card_activeCompatibilityIndex
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Fintype.card (ActiveCompatibilityIndex active chart) =
      2 * active.card := by
  have hother (i : Fin 3) :
      Fintype.card (OtherCompatibilityCoordinate i) = 2 := by
    rw [Fintype.card_subtype_compl (fun j : Fin 3 ↦ j = i)]
    simp
  rw [Fintype.card_sigma]
  simp_rw [hother]
  simp [Nat.mul_comm]

/-- Under the exact sparse-null edge count, the indexed linear and
quadratic chart generators pay at least the complete grounded-twist variable
budget.  The right side counts two compatibility generators per active
occurrence and one null generator per selected occurrence. -/
theorem universalChartGenerator_budget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (active : Finset E) (chart : active → Fin 3)
    (selected : Finset active)
    (hcard : selected.card =
      6 * (Fintype.card V - 1) - 2 * active.card) :
    groundedTwistVariableCount root ≤
      Fintype.card (ActiveCompatibilityIndex active chart) + selected.card := by
  rw [groundedTwistVariableCount_eq_six_mul_pred,
    card_activeCompatibilityIndex]
  have hbudget := sparseNull_relativeHeight_budget
    (Fintype.card V) active.card selected.card hcard
  omega

/-- The canonical finite reindexing of all grounded-twist coordinates. -/
def finiteTwistIndexEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) :
    GroundedTwistVariable root ≃ Fin (groundedTwistVariableCount root) :=
  Fintype.equivFin (GroundedTwistVariable root)

/-- The finite-variable generic chart ring over the fraction field of all
pin parameters. -/
abbrev FiniteGenericRelativeRing
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) (E : Type*) :=
  MvPolynomial (Fin (groundedTwistVariableCount root))
    (GenericPinCoefficientField E)

/-- Coefficient extension from polynomial pin parameters to their fraction
field. -/
def genericPinCoefficientHom (E : Type*) :
    PinParameterRing E →+* GenericPinCoefficientField E :=
  algebraMap (PinParameterRing E) (GenericPinCoefficientField E)

/-- First extend pin coefficients to their fraction field, then rename every
outer twist variable by the canonical finite index. -/
def finiteGenericChartHom
    {V E : Type*} [Fintype V] [DecidableEq V] (root : V) :
    RelativeRing root E →+* FiniteGenericRelativeRing root E :=
  ((MvPolynomial.renameEquiv (GenericPinCoefficientField E)
      (finiteTwistIndexEquiv root)).toRingEquiv.toRingHom).comp
    (MvPolynomial.map (genericPinCoefficientHom E))

@[simp]
theorem finiteGenericChartHom_X
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (c : GroundedTwistVariable root) :
    finiteGenericChartHom (E := E) root (X c) =
      X (finiteTwistIndexEquiv root c) := by
  simp [finiteGenericChartHom]

/-- The finite generic image of the original universal chart ideal. -/
def finiteGenericUniversalChartIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    Ideal (FiniteGenericRelativeRing root E) :=
  Ideal.map (finiteGenericChartHom root)
    (universalChartIdeal root src dst active chart selected)

/-! ## Homogeneity survives both changes of coordinates -/

private theorem finiteGenericChartHom_preserves_isHomogeneous
    {V E : Type*} [Fintype V] [DecidableEq V]
    {root : V} {f : RelativeRing root E} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (finiteGenericChartHom root f).IsHomogeneous d := by
  change
    (MvPolynomial.rename (finiteTwistIndexEquiv root)
      (MvPolynomial.map (genericPinCoefficientHom E) f)).IsHomogeneous d
  exact (hf.map (genericPinCoefficientHom E)).rename_isHomogeneous

/-- Base change to generic pin coefficients and finite reindexing preserve
the standard twist homogeneity of the universal chart ideal. -/
theorem finiteGenericUniversalChartIdeal_isHomogeneous
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active) :
    (finiteGenericUniversalChartIdeal root src dst active chart selected).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) := by
  rw [finiteGenericUniversalChartIdeal, universalChartIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
    (MvPolynomial.homogeneousSubmodule
      (Fin (groundedTwistVariableCount root))
      (GenericPinCoefficientField E))
    ((finiteGenericChartHom root) ''
      universalChartGeneratorSet root src dst active chart selected)
  intro f hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨d, hd⟩ := universalChartGeneratorSet_isHomogeneous
    root src dst active chart selected g hg
  exact ⟨d, finiteGenericChartHom_preserves_isHomogeneous hd⟩

/-! ## The transparent incidence-height obligation -/

/-- The exact local height input needed on a selected nonvanishing twist
coordinate.  It concerns only homogeneous primes over the finite generic
chart ideal which avoid that coordinate. -/
def FiniteGenericChartPrimeHeightCondition
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root) : Prop :=
  ∀ (Q : Ideal (FiniteGenericRelativeRing root E)),
    Q.IsPrime →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule
        (Fin (groundedTwistVariableCount root))
        (GenericPinCoefficientField E)) →
    finiteGenericUniversalChartIdeal root src dst active chart selected ≤ Q →
    X (finiteTwistIndexEquiv root c) ∉ Q →
    (groundedTwistVariableCount root : ℕ∞) ≤ Q.height

/-! ## Elimination on a nonvanishing twist-coordinate chart -/

/-- On the finite generic chart, the prime-height condition forces every
algebra map which makes the selected coordinate a unit to send the chart
ideal to `top`. -/
theorem map_finiteGenericUniversalChartIdeal_eq_top_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c)
    {S : Type*} [CommRing S]
    [Algebra (FiniteGenericRelativeRing root E) S]
    (hunit : IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (X (finiteTwistIndexEquiv root c)))) :
    Ideal.map (algebraMap (FiniteGenericRelativeRing root E) S)
        (finiteGenericUniversalChartIdeal
          root src dst active chart selected) = ⊤ := by
  exact NullCellulePolynomial.map_eq_top_of_homogeneousPrime_height
    (finiteGenericUniversalChartIdeal
      root src dst active chart selected)
    (finiteGenericUniversalChartIdeal_isHomogeneous
      root src dst active chart selected)
    (finiteTwistIndexEquiv root c) hheight hunit

/-- The same conclusion stated on the original universal chart ideal.  The
ring homomorphism in the conclusion is the explicit coefficient-extension,
finite-reindexing, and target-algebra composite.  Its unit hypothesis is
written on the image of the original provenance-labelled twist coordinate. -/
theorem map_universalChartIdeal_eq_top_of_primeHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (selected : Finset active)
    (c : GroundedTwistVariable root)
    (hheight : FiniteGenericChartPrimeHeightCondition
      root src dst active chart selected c)
    {S : Type*} [CommRing S]
    [Algebra (FiniteGenericRelativeRing root E) S]
    (hunit : IsUnit
      (((algebraMap (FiniteGenericRelativeRing root E) S).comp
        (finiteGenericChartHom root)) (X c))) :
    Ideal.map
        ((algebraMap (FiniteGenericRelativeRing root E) S).comp
          (finiteGenericChartHom root))
        (universalChartIdeal root src dst active chart selected) = ⊤ := by
  have hunit' : IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (X (finiteTwistIndexEquiv root c))) := by
    change IsUnit
      (algebraMap (FiniteGenericRelativeRing root E) S
        (finiteGenericChartHom root (X c))) at hunit
    rw [finiteGenericChartHom_X] at hunit
    exact hunit
  rw [← Ideal.map_map]
  exact map_finiteGenericUniversalChartIdeal_eq_top_of_primeHeight
    root src dst active chart selected c hheight hunit'

end

end UniversalHomogeneousChart

end RB31E2E
