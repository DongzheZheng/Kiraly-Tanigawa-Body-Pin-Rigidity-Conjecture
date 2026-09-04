import RB31EndToEnd.NullCellule.WittShearDistinctPrime

/-!
# Primewise selected-null height

Localization and spectator-variable transport convert a direct height theorem
for surviving coefficient minimal primes into the required selected-null
height bound.  The resulting theorem assumes only grounded collinearity-flag
semismallness.
-/

namespace RB31E2E

namespace SelectedNullHeightPrimewise

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open PolynomialPrimeTrdegHeight
open UniversalHomogeneousChart
open SelectedNullHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- A lower-height theorem for all surviving coefficient minimal primes
implies the terminal function-field inequality by the finite polynomial-prime
dimension formula. -/
theorem survivingSelectedFunctionFieldBudget_of_primewiseHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    SurvivingSelectedFunctionFieldBudget
      root src dst active angularChart selected distinctChart := by
  intro P hP hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  let t := (Algebra.trdeg ℚ
    (FractionRing (TwistCoefficientRing root ⧸ P))).toNat
  have hformula := polynomialPrime_height_add_fractionTrdeg_eq_natCard P
  have hadd : (selected.card : ℕ∞) + (t : ℕ∞) ≤
      (Nat.card (GroundedTwistVariable root) : ℕ∞) := by
    calc
      (selected.card : ℕ∞) + (t : ℕ∞) ≤
          P.height + (t : ℕ∞) :=
        by simpa [add_comm] using
          (add_le_add_right (hHeight P hP hAngular hDistinct) (t : ℕ∞))
      _ = (Nat.card (GroundedTwistVariable root) : ℕ∞) := hformula
  have hn : t + selected.card ≤ Nat.card (GroundedTwistVariable root) := by
    apply ENat.coe_le_coe.mp
    simpa only [Nat.cast_add, add_comm] using hadd
  simpa [t, add_comm] using hn

/-- Public localization/spectator bridge whose input is direct primewise
height, not a full-twist function-field budget. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  exact incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_budget
    root src dst active hLoop angularChart selected distinctChart
      (survivingSelectedFunctionFieldBudget_of_primewiseHeight
        root src dst active angularChart selected distinctChart hHeight)

/-- The selected-null localized lower-height bound required by the incidence
transfer follows directly from grounded PF semismallness.  No
`SurvivingSelectedFunctionFieldBudget`, selected-null height, or generic
fibre identity is a premise. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (GroundedTwistSplit.SpatialVariable root)) :
    let selected := SparseNullIncidence.selectedSkeletonOccurrences
      src dst active hLoop F hRepresented
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  classical
  dsimp only
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  apply incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    root src dst active hLoop angularChart selected distinctChart
  intro P hP _hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  have hF :=
    WittShearDistinctPrime.coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented distinctChart P hP hDistinct hPF
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented]
  exact hF.symm.le

end

end SelectedNullHeightPrimewise

end RB31E2E
