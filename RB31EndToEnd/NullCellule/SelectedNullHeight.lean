import RB31EndToEnd.Algebra.PolynomialPrimeTrdegHeight
import RB31EndToEnd.Incidence.PinOuterFullProvenanceHeightTransfer
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Selected Split--Klein null height from a function-field budget

This file isolates the commutative-algebra part of the direct
semismallness-to-height argument.  The selected null equations are first
defined literally in the grounded twist polynomial ring.  We then prove
that the target ideal is obtained from this ideal by exactly three standard
operations:

* localization at the active angular denominator;
* adjoining the retained pin variables, which are polynomial spectators;
* localization at the complete distinctness denominator.

Minimal primes and their heights are transported through all three steps.
The sole input of the public theorem is a function-field dimension budget
for the surviving minimal primes of the literal grounded selected-null
ideal.  It is a theorem parameter, not a field of an opaque structure.
-/

namespace RB31E2E

namespace SelectedNullHeight

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open PolynomialPrimeTrdegHeight
open UniversalHomogeneousChart

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The literal grounded selected-null ideal -/

/-- One selected Split--Klein null equation before either localization and
before any retained pin variables are adjoined. -/
def coefficientNullEquation
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) :
    TwistCoefficientRing root :=
  Twist.splitKlein (coefficientRelativeTwist root src dst e)

/-- The selected null ideal in the literal grounded twist polynomial ring. -/
def coefficientSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) : Ideal (TwistCoefficientRing root) :=
  Ideal.span (Set.range (fun e : SelectedOccurrence active selected ↦
    coefficientNullEquation root src dst e.1.1))

/-- Generalized Krull height theorem for a minimal prime of the literal
selected-null ideal. -/
theorem coefficientMinimalPrime_height_le_selectedCard
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active)
    (P : Ideal (TwistCoefficientRing root))
    (hP : P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes) :
    P.height ≤ (selected.card : ℕ∞) := by
  classical
  let g : SelectedOccurrence active selected →
      TwistCoefficientRing root :=
    fun e ↦ coefficientNullEquation root src dst e.1.1
  have hPspan :
      P ∈ (Ideal.span (Set.range g)).minimalPrimes := by
    simpa only [coefficientSelectedNullIdeal, g] using hP
  have hKrull :
      P.height ≤ ((Set.range g).ncard : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span
      (Set.finite_range g) hPspan
  have hncard : (Set.range g).ncard ≤ selected.card := by
    rw [← Set.image_univ]
    simpa using Set.ncard_image_le (f := g) (s := Set.univ)
  exact hKrull.trans (by exact_mod_cast hncard)

/-- The same ideal after the active-angular localization. -/
def angularSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal (AngularCoefficientLocalization
      root src dst active angularChart) :=
  Ideal.map
    (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active angularChart))
    (coefficientSelectedNullIdeal root src dst active selected)

theorem algebraMap_coefficientNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active angularChart)
        (coefficientNullEquation root src dst e) =
      Twist.splitKlein
        (localizedCoefficientRelativeTwist
          root src dst active angularChart e) := by
  rw [coefficientNullEquation, localizedCoefficientRelativeTwist,
    map_splitKlein_local]

theorem C_algebraMap_coefficientNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    C (algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active angularChart)
        (coefficientNullEquation root src dst e)) =
      retainedNullEquation root src dst active angularChart e := by
  letI : CommRing (AngularCoefficientLocalization
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  rw [algebraMap_coefficientNullEquation]
  exact map_splitKlein_local
    (C : AngularCoefficientLocalization
        root src dst active angularChart →+*
      RetainedCoefficientRing root src dst active angularChart)
    (localizedCoefficientRelativeTwist
      root src dst active angularChart e)

/-- The retained selected-null ideal is exactly the constant polynomial
extension of the angular-localized literal ideal. -/
theorem retainedSelectedNullIdeal_eq_map_C_angularSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    retainedSelectedNullIdeal root src dst active angularChart selected =
      Ideal.map
        (C : AngularCoefficientLocalization
            root src dst active angularChart →+*
          RetainedCoefficientRing root src dst active angularChart)
        (angularSelectedNullIdeal
          root src dst active angularChart selected) := by
  rw [retainedSelectedNullIdeal, angularSelectedNullIdeal,
    coefficientSelectedNullIdeal, Ideal.map_map, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨coefficientNullEquation root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    simpa using C_algebraMap_coefficientNullEquation
      root src dst active angularChart e.1.1
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    refine ⟨e, ?_⟩
    simpa using (C_algebraMap_coefficientNullEquation
      root src dst active angularChart e.1.1).symm

/-! ## Polynomial spectators -/

/-- A minimal prime of a constant polynomial extension is itself the
constant extension of its contraction.  In particular, the contraction is
a minimal prime of the original ideal. -/
theorem minimalPrime_map_C_contract
    {A τ : Type*} [CommRing A]
    (I : Ideal A) (Q : Ideal (MvPolynomial τ A))
    (hQ : Q ∈ (Ideal.map (C : A →+* MvPolynomial τ A) I).minimalPrimes) :
    let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
    P ∈ I.minimalPrimes ∧
      Ideal.map (C : A →+* MvPolynomial τ A) P = Q := by
  classical
  let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
  have hQprime : Q.IsPrime := hQ.1.1
  letI : Q.IsPrime := hQprime
  have hPprime : P.IsPrime := Ideal.IsPrime.comap _
  letI : P.IsPrime := hPprime
  have hIP : I ≤ P := by
    exact Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hmapPprime :
      (Ideal.map (C : A →+* MvPolynomial τ A) P).IsPrime := by
    simpa [ActivePinPrimeHeight.basePrimeCoordinateIdeal,
      NullCellulePolynomial.coordinateVariableIdeal] using
      (ActivePinPrimeHeight.basePrimeCoordinateIdeal_isPrime
        (σ := τ) P (∅ : Set τ))
  have hmapP_le_Q :
      Ideal.map (C : A →+* MvPolynomial τ A) P ≤ Q :=
    Ideal.map_comap_le
  have hmapP_eq :
      Ideal.map (C : A →+* MvPolynomial τ A) P = Q := by
    apply le_antisymm hmapP_le_Q
    exact hQ.2 ⟨hmapPprime, Ideal.map_mono hIP⟩ hmapP_le_Q
  refine ⟨⟨⟨hPprime, hIP⟩, ?_⟩, hmapP_eq⟩
  intro P' hP' hP'P
  letI : P'.IsPrime := hP'.1
  have hmapP'prime :
      (Ideal.map (C : A →+* MvPolynomial τ A) P').IsPrime := by
    simpa [ActivePinPrimeHeight.basePrimeCoordinateIdeal,
      NullCellulePolynomial.coordinateVariableIdeal] using
      (ActivePinPrimeHeight.basePrimeCoordinateIdeal_isPrime
        (σ := τ) P' (∅ : Set τ))
  have hmapP'Q :
      Ideal.map (C : A →+* MvPolynomial τ A) P' ≤ Q := by
    rw [← hmapP_eq]
    exact Ideal.map_mono hP'P
  have hQmapP' : Q ≤ Ideal.map (C : A →+* MvPolynomial τ A) P' :=
    hQ.2 ⟨hmapP'prime, Ideal.map_mono hP'.2⟩ hmapP'Q
  change P ≤ P'
  rw [← ActivePinPrimeHeight.comap_map_C_eq_self (σ := τ) P']
  exact Ideal.comap_mono hQmapP'

/-- Retained pin variables do not alter the height of a minimal prime. -/
theorem minimalPrime_map_C_height_eq
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (I : Ideal A) (Q : Ideal (MvPolynomial τ A))
    (hQ : Q ∈ (Ideal.map (C : A →+* MvPolynomial τ A) I).minimalPrimes) :
    Q.height =
      (Ideal.comap (C : A →+* MvPolynomial τ A) Q).height := by
  let P := Ideal.comap (C : A →+* MvPolynomial τ A) Q
  obtain ⟨hP, hmap⟩ := minimalPrime_map_C_contract I Q hQ
  letI : P.IsPrime := hP.1.1
  calc
    Q.height = (Ideal.map (C : A →+* MvPolynomial τ A) P).height := by
      rw [hmap]
    _ = P.height := ActivePinPrimeHeight.height_map_C_eq (σ := τ) P
    _ = (Ideal.comap (C : A →+* MvPolynomial τ A) Q).height := rfl

/-! ## Prime height from the PF function-field inequality -/

/-- The polynomial prime height formula converts a finite function-field
dimension budget into the required lower height bound. -/
theorem polynomialPrime_height_ge_of_fractionTrdeg_add_le
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (m : ℕ)
    (hbudget :
      (Algebra.trdeg k
        (FractionRing (MvPolynomial ι k ⧸ P))).toNat + m ≤
        Nat.card ι) :
    (m : ℕ∞) ≤ P.height := by
  let t := (Algebra.trdeg k
      (FractionRing (MvPolynomial ι k ⧸ P))).toNat
  have hcast : (m : ℕ∞) + (t : ℕ∞) ≤ (Nat.card ι : ℕ∞) := by
    exact_mod_cast (by simpa [add_comm] using hbudget)
  have hformula := polynomialPrime_height_add_fractionTrdeg_eq_natCard P
  change (m : ℕ∞) ≤ P.height
  rw [← ENat.add_le_add_iff_right (by simp : (t : ℕ∞) ≠ ⊤)]
  simpa [t, add_comm, add_left_comm, add_assoc, hformula] using hcast

/-! ## Function-field budget and height -/

/-- The terminal function-field inequality supplied by the projection--fibre
argument.  It is quantified over the actual minimal
primes of the literal selected-null ideal and only over branches surviving
both provenance opens. -/
def SurvivingSelectedFunctionFieldBudget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : Prop :=
  ∀ (P : Ideal (TwistCoefficientRing root)),
    P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes →
    activeAngularDenominator root src dst active angularChart ∉ P →
    coefficientDistinctnessDenominator root distinctChart ∉ P →
    (Algebra.trdeg ℚ
      (FractionRing (TwistCoefficientRing root ⧸ P))).toNat +
        selected.card ≤ Nat.card (GroundedTwistVariable root)

/-- The surviving function-field inequality implies the selected-null height
bound used by the incidence transfer theorem. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_budget
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (_hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hPF : SurvivingSelectedFunctionFieldBudget
      root src dst active angularChart selected distinctChart) :
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  classical
  let R₀ := TwistCoefficientRing root
  let I₀ : Ideal R₀ := coefficientSelectedNullIdeal
    root src dst active selected
  let dₐ : R₀ := activeAngularDenominator
    root src dst active angularChart
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let Iₐ : Ideal A := Ideal.map (algebraMap R₀ A) I₀
  let B := RetainedCoefficientRing
    root src dst active angularChart
  let Ib : Ideal B := retainedSelectedNullIdeal
    root src dst active angularChart selected
  let db : B := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away db
  let It : Ideal T := Ideal.map (algebraMap B T) Ib
  letI : IsDomain A := angularCoefficientLocalizationIsDomain
    root src dst active angularChart _hLoop
  letI : Nontrivial B := inferInstance
  letI : CommRing B := inferInstance
  change (selected.card : ℕ∞) ≤ It.height
  rw [Ideal.height]
  apply le_iInf
  intro Q
  apply le_iInf
  intro hQ
  letI : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  let Qb : Ideal B := Ideal.comap (algebraMap B T) Q
  have hQb : Qb ∈ Ib.minimalPrimes := by
    have hm := (IsLocalization.minimalPrimes_map
      (Submonoid.powers db) T Ib)
    have : Q ∈ (Ideal.map (algebraMap B T) Ib).minimalPrimes := hQ
    rw [hm] at this
    exact this
  letI : Qb.IsPrime := hQb.1.1
  have hIb : Ib = Ideal.map (C : A →+* B) Iₐ := by
    exact retainedSelectedNullIdeal_eq_map_C_angularSelectedNullIdeal
      root src dst active angularChart selected
  have hQb' : Qb ∈ (Ideal.map (C : A →+* B) Iₐ).minimalPrimes := by
    simpa [hIb] using hQb
  let Pₐ : Ideal A := Ideal.comap (C : A →+* B) Qb
  have hPₐ : Pₐ ∈ Iₐ.minimalPrimes :=
    (minimalPrime_map_C_contract Iₐ Qb hQb').1
  have hmapPₐ : Ideal.map (C : A →+* B) Pₐ = Qb :=
    (minimalPrime_map_C_contract Iₐ Qb hQb').2
  letI : Pₐ.IsPrime := hPₐ.1.1
  let P₀ : Ideal R₀ := Ideal.comap (algebraMap R₀ A) Pₐ
  have hP₀ : P₀ ∈ I₀.minimalPrimes := by
    have hm := (IsLocalization.minimalPrimes_map
      (Submonoid.powers dₐ) A I₀)
    have : Pₐ ∈ (Ideal.map (algebraMap R₀ A) I₀).minimalPrimes := hPₐ
    rw [hm] at this
    exact this
  letI : P₀.IsPrime := hP₀.1.1
  have hdₐ : dₐ ∉ P₀ := by
    have hdisj : Disjoint (Submonoid.powers dₐ : Set R₀) (P₀ : Set R₀) :=
      (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers dₐ) A Pₐ).mp (inferInstance : Pₐ.IsPrime) |>.2
    intro hd
    exact hdisj.le_bot ⟨Submonoid.mem_powers dₐ, hd⟩
  have hdb : db ∉ Qb := by
    have hdisj : Disjoint (Submonoid.powers db : Set B) (Qb : Set B) :=
      (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers db) T Q).mp (inferInstance : Q.IsPrime) |>.2
    intro hd
    exact hdisj.le_bot ⟨Submonoid.mem_powers db, hd⟩
  have hddist : coefficientDistinctnessDenominator root distinctChart ∉ P₀ := by
    intro hd
    apply hdb
    dsimp [db, retainedDistinctnessDenominator]
    rw [← hmapPₐ]
    apply Ideal.mem_map_of_mem (C : A →+* B)
    have himg := Ideal.mem_map_of_mem (algebraMap R₀ A) hd
    rw [IsLocalization.map_comap (Submonoid.powers dₐ) A Pₐ] at himg
    exact himg
  have hbase : (selected.card : ℕ∞) ≤ P₀.height := by
    exact polynomialPrime_height_ge_of_fractionTrdeg_add_le
      P₀ selected.card (hPF P₀ hP₀ hdₐ hddist)
  have hangular : Pₐ.height = P₀.height := by
    rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    exact (IsLocalization.primeHeight_comap
      (Submonoid.powers dₐ) Pₐ).symm
  have hspectator : Qb.height = Pₐ.height := by
    simpa [Pₐ] using minimalPrime_map_C_height_eq Iₐ Qb hQb'
  have hdistinct : Q.height = Qb.height := by
    rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    exact (IsLocalization.primeHeight_comap
      (Submonoid.powers db) Q).symm
  calc
    (selected.card : ℕ∞) ≤ P₀.height := hbase
    _ = Pₐ.height := hangular.symm
    _ = Qb.height := hspectator.symm
    _ = Q.height := hdistinct.symm
    _ = Q.primeHeight := Ideal.height_eq_primeHeight Q

end

end SelectedNullHeight

end RB31E2E
