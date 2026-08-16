import RB31EndToEnd.NullCellule.SelectedDirectionFibre
import RB31EndToEnd.Linear.FiniteRowSpanStress

/-!
# Height ledger for a split selected direction component

This file combines the coefficient-prime dimension formula, the exact
generic linear fibre, and direction-matrix rank--nullity.  The only
mathematical input is the global grounded function-field semismallness
theorem; no selected-null height or terminal twist-field budget is assumed.
-/

namespace RB31E2E

namespace SelectedDirectionHeight

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open PolynomialPrimeTrdegHeight
open GroundedTwistSplit
open SelectedDirectionFibre
open CoefficientLinearFibre
open MinimalPrimeLinearFibre
open UniversalHomogeneousChart

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- A minimal component of the split selected-null system has the full edge
height once the grounded PF function-field inequality is available for all
coordinate-generated distinct placements. -/
theorem splitMinimalPrime_height_ge_edgeCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (P : Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ))) [P.IsPrime]
    [(coefficientContraction P).IsPrime]
    (hP : P ∈ (splitSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hInjective : Function.Injective
      (quotientPlacement root (coefficientContraction P)))
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (SpatialVariable root)) :
    (F.card : ℕ∞) ≤ P.height := by
  classical
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  let τ := SpatialVariable root
  let A := MvPolynomial τ ℚ
  let p : Ideal A := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let q := coefficientQuotientMap (τ := τ) p
  let ℓ : MvPolynomial τ B →+* MvPolynomial τ K :=
    MvPolynomial.map (algebraMap B K)
  let PL : Ideal (MvPolynomial τ K) :=
    Ideal.map ℓ (Ideal.map q P)
  let a : V → Fin 3 → K := quotientPlacement root p
  let rowA : SelectedOccurrence active selected → τ → A :=
    fun e ↦ occurrenceDirectionRow root src dst
      (coefficientPlacement (k := ℚ) root) e.1.1
  let rowK : SelectedOccurrence active selected → τ → K :=
    fun e x ↦ algebraMap B K
      (Ideal.Quotient.mk p (rowA e x))
  let rowDirection : SelectedOccurrence active selected → τ → K :=
    fun e ↦ occurrenceDirectionRow root src dst a e.1.1
  have hIeq : splitSelectedNullIdeal root src dst active selected =
      linearFormIdealOver rowA := by
    exact splitSelectedNullIdeal_eq_linearFormIdealOver
      root src dst active hLoop selected
  have hPlinear : P ∈ (linearFormIdealOver rowA).minimalPrimes := by
    rw [← hIeq]
    exact hP
  have hgeneric : PL = LinearFormIdeal.linearFormIdeal rowK := by
    exact fractionFibrePrime_eq_linearFormIdeal rowA P hPlinear
  have hrow : rowK = rowDirection := by
    funext e x
    exact map_occurrenceDirectionRow root src dst e.1.1 p x
  have hPLlinear : PL = LinearFormIdeal.linearFormIdeal rowDirection := by
    rw [hgeneric, hrow]
  have hrange : Set.range rowDirection =
      Set.range (fun f : F ↦
        GroundedDirectionConstraint.groundedDirectionRow root a f.1) := by
    exact range_selectedOccurrenceRows_eq_range_groundedDirectionRows
      root src dst active hLoop F hRepresented a
  have hlinearHeight :
      (Module.finrank K
        (Submodule.span K (Set.range rowDirection)) : ℕ∞) ≤
        PL.height := by
    rw [hPLlinear]
    exact LinearFormIdeal.finrank_span_le_linearFormIdeal_height rowDirection
  let groundRow : F → τ → K := fun f ↦
    GroundedDirectionConstraint.groundedDirectionRow root a f.1
  have hspanStress :
      Module.finrank K (Submodule.span K (Set.range groundRow)) +
          DirectionStress.directionStressDim F a = F.card := by
    have hs := FiniteRowSystem.finrank_span_add_stressDim_eq_card groundRow
    have hstressEq : FiniteRowSystem.stressDim groundRow =
        DirectionStress.directionStressDim F a := by
      exact GroundedDirectionConstraint.stressDim_eq_directionStressDim
        root F a
    rw [hstressEq] at hs
    calc
      Module.finrank K (Submodule.span K (Set.range groundRow)) +
          DirectionStress.directionStressDim F a = Fintype.card F := hs
      _ = F.card := Fintype.card_coe F
  have hrankNullity :
      DirectionStress.directionStressDim F a +
          Module.finrank K
            (Submodule.span K (Set.range rowDirection)) = F.card := by
    rw [hrange]
    rw [add_comm]
    exact hspanStress
  have hgenerated : IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ := by
    exact quotientPlacement_generated root p
  have hroot : a root = 0 := quotientPlacement_root root p
  have hPFnat : DirectionStress.directionStressDim F a +
      (Algebra.trdeg ℚ K).toNat ≤ Nat.card τ := by
    exact hPF a hroot hInjective hgenerated
  let t := (Algebra.trdeg ℚ K).toNat
  have hpFormula : p.height + (t : ℕ∞) = (Nat.card τ : ℕ∞) := by
    exact polynomialPrime_height_add_fractionTrdeg_eq_natCard p
  have hPFcast :
      (DirectionStress.directionStressDim F a : ℕ∞) + (t : ℕ∞) ≤
        (Nat.card τ : ℕ∞) := by
    exact_mod_cast hPFnat
  have hstress :
      (DirectionStress.directionStressDim F a : ℕ∞) ≤ p.height := by
    rw [← ENat.add_le_add_iff_right (by simp : (t : ℕ∞) ≠ ⊤)]
    calc
      (DirectionStress.directionStressDim F a : ℕ∞) + (t : ℕ∞) ≤
          (Nat.card τ : ℕ∞) := hPFcast
      _ = p.height + (t : ℕ∞) := hpFormula.symm
  have hheight : P.height = p.height + PL.height := by
    exact polynomialPrime_height_eq_contractionHeight_add_fractionFibreHeight P
  rw [hheight, ← hrankNullity, Nat.cast_add]
  exact add_le_add hstress hlinearHeight

end

end SelectedDirectionHeight

end RB31E2E
