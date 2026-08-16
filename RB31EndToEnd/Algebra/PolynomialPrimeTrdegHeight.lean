import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Heights of primes in finite polynomial rings

This file develops the commutative-algebra bridge needed to turn a
function-field dimension estimate for a selected-null component into a
height estimate in its ambient finite polynomial ring.

The first kernel theorem records the equidimensionality of closed points of
finite affine space over a field.  It is proved directly from the one-variable
height formula and the Jacobson property of finite polynomial rings; it does
not assume catenarity or a dimension formula as an extra premise.
-/

namespace RB31E2E

namespace PolynomialPrimeTrdegHeight

noncomputable section

open MvPolynomial

/-- The contraction of a polynomial-ring ideal to its coefficient ring. -/
def coefficientContraction {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) : Ideal A :=
  P.comap (MvPolynomial.C : A →+* MvPolynomial τ A)

/-! ## Coordinate transcendence bases in polynomial quotients -/

/-- The image of a polynomial coordinate in a quotient. -/
def quotientCoordinate {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) (i : ι) :
    MvPolynomial ι k ⧸ P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

/-- A polynomial quotient is generated, as an algebra, by the images of its
coordinate variables. -/
theorem adjoin_range_quotientCoordinate
    {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) :
    Algebra.adjoin k (Set.range (quotientCoordinate P)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  rintro b -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f, ?_⟩
  change MvPolynomial.aeval
    (fun d : ι ↦ Ideal.Quotient.mk P (MvPolynomial.X d)) f =
      Ideal.Quotient.mk P f
  rw [← MvPolynomial.mkₐ_eq_aeval P]
  rfl

/-- Every prime quotient of a finite polynomial ring admits a
transcendence basis chosen from the images of the original coordinates.
This is an existence theorem, not a premise of the later height formula. -/
theorem exists_coordinate_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ t : Set (MvPolynomial ι k ⧸ P),
      t ⊆ Set.range (quotientCoordinate P) ∧
      IsTranscendenceBasis k
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
  let B := MvPolynomial ι k ⧸ P
  let x : ι → B := quotientCoordinate P
  have htop : Algebra.adjoin k (Set.range x) = ⊤ :=
    adjoin_range_quotientCoordinate P
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin k (Set.range x) := by
      rw [htop]
      trivial
    exact isAlgebraic_algebraMap
      (⟨b, hb⟩ : Algebra.adjoin k (Set.range x))
  exact exists_isTranscendenceBasis_subset (R := k) (A := B)
    (Set.range x)

/-- Index-level version: one can choose a subset of the original variable
indices whose quotient-coordinate images form a transcendence basis. -/
theorem exists_coordinateIndex_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ S : Set ι,
      IsTranscendenceBasis k
        (fun i : S ↦ quotientCoordinate P i) := by
  obtain ⟨t, ht, htb⟩ := exists_coordinate_transcendenceBasis P
  let g : t → ι := fun y ↦
    Classical.choose (ht y.property)
  have hg (y : t) : quotientCoordinate P (g y) = y :=
    Classical.choose_spec (ht y.property)
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    simpa [hg] using congrArg (quotientCoordinate P) hab
  let S : Set ι := Set.range g
  let e : t ≃ S := Equiv.ofInjective g hginj
  have heq :
      (fun i : S ↦ quotientCoordinate P i) ∘ e =
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
    funext y
    exact hg y
  refine ⟨S, ?_⟩
  exact (isTranscendenceBasis_equiv' e heq).mp htb

/-- Split a finite variable set into a chosen coordinate set and its
complement, viewing the latter as polynomial variables over the former. -/
def coordinateSplitEquiv {k ι : Type*} [CommRing k] (S : Set ι) :
    MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k) ≃ₐ[k]
      MvPolynomial ι k := by
  classical
  exact (MvPolynomial.sumAlgEquiv k (Sᶜ : Set ι) S).symm.trans
    (MvPolynomial.renameEquiv k
      ((Equiv.sumComm (Sᶜ : Set ι) S).trans
        (Equiv.Set.sumCompl S)))

/-- Pull a polynomial prime back along the coordinate splitting
equivalence. -/
def coordinateSplitPrime {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) (S : Set ι) :
    Ideal (MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) :=
  P.comap (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom

theorem coordinateSplitPrime_isPrime
    {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι) :
    (coordinateSplitPrime P S).IsPrime := by
  exact Ideal.comap_isPrime
    (f := (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom)
    (K := P)

/-- On the coefficient-polynomial subring, the coordinate splitting
equivalence is simply renaming by the subtype inclusion. -/
theorem coordinateSplitEquiv_comp_C
    {k ι : Type*} [CommRing k] (S : Set ι) :
    (coordinateSplitEquiv (k := k) S).toAlgHom.toRingHom.comp
      (MvPolynomial.C :
        MvPolynomial S k →+*
          MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) =
      (MvPolynomial.rename ((↑) : S → ι)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coordinateSplitEquiv]
  · intro i
    classical
    simp only [coordinateSplitEquiv, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_X, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
      AlgEquiv.coe_trans, Function.comp_apply,
      MvPolynomial.sumAlgEquiv_symm_apply, iterToSum_C_X,
      renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply,
      Sum.swap_inr, Equiv.Set.sumCompl_apply_inl]

/-- Algebraic independence of the chosen quotient coordinates says exactly
that the split prime has zero coefficient contraction. -/
theorem coordinateSplitPrime_contraction_eq_bot
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : AlgebraicIndependent k
      (fun i : S ↦ quotientCoordinate P i)) :
    coefficientContraction (coordinateSplitPrime P S) = ⊥ := by
  let f : MvPolynomial S k →ₐ[k] (MvPolynomial ι k ⧸ P) :=
    (Ideal.Quotient.mkₐ k P).comp
      (MvPolynomial.rename ((↑) : S → ι))
  have hf : f = MvPolynomial.aeval
      (fun i : S ↦ quotientCoordinate P i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f, quotientCoordinate]
  have hfinj : Function.Injective f := by
    rw [hf]
    exact algebraicIndependent_iff_injective_aeval.mp hS
  rw [coefficientContraction, coordinateSplitPrime,
    Ideal.comap_comap, coordinateSplitEquiv_comp_C]
  rw [← @Ideal.mk_ker _ _ P,
    RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hfinj

/-- Evaluation of the chosen coordinate-polynomial ring in the prime
quotient. -/
def coordinateAeval {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) (S : Set ι) :
    MvPolynomial S k →ₐ[k] (MvPolynomial ι k ⧸ P) :=
  MvPolynomial.aeval (fun i : S ↦ quotientCoordinate P i)

/-- The fraction-field map induced by evaluating a polynomial in an
algebraically independent family of quotient coordinates. -/
def coordinateFractionHom {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : AlgebraicIndependent k
      (fun i : S ↦ quotientCoordinate P i)) :
    FractionRing (MvPolynomial S k) →ₐ[k]
      FractionRing (MvPolynomial ι k ⧸ P) :=
  let B := MvPolynomial ι k ⧸ P
  let L := FractionRing B
  let gL : MvPolynomial S k →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp (coordinateAeval P S)
  IsFractionRing.liftAlgHom (g := gL)
    ((FaithfulSMul.algebraMap_injective B L).comp
      (algebraicIndependent_iff_injective_aeval.mp hS))

/-- A coordinate transcendence basis makes the fraction field of the prime
quotient algebraic over the fraction field of the basis-coordinate
polynomial ring.  The algebra structure on the target fraction field is the
canonical lift of coordinate evaluation. -/
theorem fractionRing_quotient_isAlgebraic_over_coordinateBasis
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    let A := MvPolynomial S k
    let B := MvPolynomial ι k ⧸ P
    let K := FractionRing A
    let L := FractionRing B
    let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
    @Algebra.IsAlgebraic K L
      (inferInstance : CommRing K) (inferInstance : Ring L)
      κ.toRingHom.toAlgebra := by
  dsimp only
  let A := MvPolynomial S k
  let B := MvPolynomial ι k ⧸ P
  let K := FractionRing A
  let L := FractionRing B
  let g : A →ₐ[k] B := coordinateAeval P S
  have hg : Function.Injective g :=
    algebraicIndependent_iff_injective_aeval.mp hS.1
  letI : Algebra A B := g.toRingHom.toAlgebra
  have hAB : Algebra.IsAlgebraic A B := by
    let E := hS.1.aevalEquiv
    haveI : Algebra.IsAlgebraic
        (Algebra.adjoin k
          (Set.range (fun i : S ↦ quotientCoordinate P i))) B :=
      hS.isAlgebraic
    apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
      (f := E.toRingHom) (g := RingHom.id B)
      E.surjective Function.injective_id
    apply DFunLike.ext _ _
    intro a
    change algebraMap
      (Algebra.adjoin k
        (Set.range (fun i : S ↦ quotientCoordinate P i))) B
        (hS.1.aevalEquiv a) =
      MvPolynomial.aeval
        (fun i : S ↦ quotientCoordinate P i) a
    exact hS.1.algebraMap_aevalEquiv a
  let gL : A →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp g
  have hBL : Algebra.IsAlgebraic B L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hAL : Algebra.IsAlgebraic A L :=
    Algebra.IsAlgebraic.trans A B L
  have hgL : Function.Injective gL :=
    (FaithfulSMul.algebraMap_injective B L).comp hg
  let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
  letI : Algebra K L := κ.toRingHom.toAlgebra
  letI : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change gL a = κ (algebraMap A K a)
      exact (IsFractionRing.lift_algebraMap hgL a).symm
  exact IsFractionRing.comap_isAlgebraic_iff.mp hAL

/-- After localizing the chosen coordinate-transcendence-basis ring, the
remaining-coordinate quotient is algebraic.  This is the generic-fibre
statement that converts coordinate provenance into a height computation. -/
theorem coordinateSplitPrime_genericFibre_trdeg_eq_zero
    {k ι : Type*} [Field k]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    Algebra.trdeg (FractionRing (MvPolynomial S k))
      (MvPolynomial (Sᶜ : Set ι)
          (FractionRing (MvPolynomial S k)) ⧸
        (coordinateSplitPrime P S).map
          (MvPolynomial.map
            (algebraMap (MvPolynomial S k)
              (FractionRing (MvPolynomial S k))))) = 0 := by
  let A := MvPolynomial S k
  let B := MvPolynomial ι k ⧸ P
  let K := FractionRing A
  let L := FractionRing B
  let R := MvPolynomial (Sᶜ : Set ι) A
  let RK := MvPolynomial (Sᶜ : Set ι) K
  let E : R ≃ₐ[k] MvPolynomial ι k := coordinateSplitEquiv S
  let J : Ideal R := coordinateSplitPrime P S
  let Q : Ideal RK :=
    J.map (MvPolynomial.map (algebraMap A K))
  let g : A →ₐ[k] B := coordinateAeval P S
  have hg : Function.Injective g :=
    algebraicIndependent_iff_injective_aeval.mp hS.1
  let gL : A →ₐ[k] L :=
    (IsScalarTower.toAlgHom k B L).comp g
  have hgL : Function.Injective gL :=
    (FaithfulSMul.algebraMap_injective B L).comp hg
  let κ : K →ₐ[k] L := coordinateFractionHom P S hS.1
  letI : Algebra K L := κ.toRingHom.toAlgebra
  have hκ (a : A) :
      κ (algebraMap A K a) = algebraMap B L (g a) := by
    change κ (algebraMap A K a) = gL a
    exact IsFractionRing.lift_algebraMap hgL a
  have hKL : Algebra.IsAlgebraic K L := by
    simpa [A, B, K, L, κ] using
      fractionRing_quotient_isAlgebraic_over_coordinateBasis P S hS
  letI : Algebra.IsAlgebraic K L := hKL
  let y : (Sᶜ : Set ι) → L := fun i ↦
    algebraMap B L (quotientCoordinate P i)
  let φ : RK →ₐ[K] L := MvPolynomial.aeval y
  have hEcoeff (a : A) :
      Ideal.Quotient.mk P (E (MvPolynomial.C a)) = g a := by
    calc
      Ideal.Quotient.mk P (E (MvPolynomial.C a)) =
          Ideal.Quotient.mk P
            (MvPolynomial.rename ((↑) : S → ι) a) := by
        congr 1
        exact DFunLike.congr_fun
          (coordinateSplitEquiv_comp_C (k := k) S) a
      _ = MvPolynomial.aeval
          (fun i : ι ↦ quotientCoordinate P i)
          (MvPolynomial.rename ((↑) : S → ι) a) := by
        change (Ideal.Quotient.mkₐ k P)
            (MvPolynomial.rename ((↑) : S → ι) a) = _
        rw [MvPolynomial.mkₐ_eq_aeval]
        rfl
      _ = MvPolynomial.aeval
          (fun i : S ↦ quotientCoordinate P i) a := by
        rw [MvPolynomial.aeval_rename]
        rfl
      _ = g a := rfl
  have hEX (i : (Sᶜ : Set ι)) :
      E (MvPolynomial.X i) = MvPolynomial.X (i : ι) := by
    classical
    change MvPolynomial.rename
      ((Equiv.Set.sumCompl S) ∘ Sum.swap)
        (MvPolynomial.iterToSum k (Sᶜ : Set ι) S
          (MvPolynomial.X i)) = MvPolynomial.X (i : ι)
    rw [MvPolynomial.iterToSum_X, MvPolynomial.rename_X]
    rfl
  have hcomp :
      φ.toRingHom.comp (MvPolynomial.map (algebraMap A K)) =
        (algebraMap B L).comp
          ((Ideal.Quotient.mk P).comp E.toRingEquiv.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply]
      calc
        φ.toRingHom
            (MvPolynomial.map (algebraMap A K) (MvPolynomial.C a)) =
            κ (algebraMap A K a) := by
          rw [MvPolynomial.map_C]
          change MvPolynomial.aeval y
            (MvPolynomial.C (algebraMap A K a)) = _
          rw [MvPolynomial.aeval_C]
          rfl
        _ = algebraMap B L (g a) := hκ a
        _ = algebraMap B L
            (Ideal.Quotient.mk P (E (MvPolynomial.C a))) := by
          rw [hEcoeff]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply]
      calc
        φ.toRingHom
            (MvPolynomial.map (algebraMap A K) (MvPolynomial.X i)) =
            y i := by
          rw [MvPolynomial.map_X]
          change MvPolynomial.aeval y (MvPolynomial.X i) = y i
          rw [MvPolynomial.aeval_X]
        _ = algebraMap B L (quotientCoordinate P i) := rfl
        _ = algebraMap B L
            (Ideal.Quotient.mk P (E (MvPolynomial.X i))) := by
          rw [hEX]
          rfl
  letI : Algebra R RK := MvPolynomial.algebraMvPolynomial
  let M : Submonoid R :=
    (nonZeroDivisors A).map
      (MvPolynomial.C : A →+* R)
  have hcomap :
      (RingHom.ker φ.toRingHom).comap (algebraMap R RK) = J := by
    apply Ideal.ext
    intro r
    change φ ((algebraMap R RK) r) = 0 ↔ r ∈ J
    change φ (MvPolynomial.map (algebraMap A K) r) = 0 ↔ r ∈ J
    have hrcomp := DFunLike.congr_fun hcomp r
    change φ (MvPolynomial.map (algebraMap A K) r) =
      algebraMap B L (Ideal.Quotient.mk P (E r)) at hrcomp
    rw [hrcomp]
    constructor
    · intro hr
      have hr' : Ideal.Quotient.mk P (E r) = 0 :=
        (FaithfulSMul.algebraMap_injective B L) (by
          rw [map_zero]
          exact hr)
      have : E r ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hr'
      exact this
    · intro hr
      have hr' : Ideal.Quotient.mk P (E r) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      simpa using congrArg (algebraMap B L) hr'
  have hker : RingHom.ker φ.toRingHom = Q := by
    have hloc := IsLocalization.map_comap M RK
      (RingHom.ker φ.toRingHom)
    rw [hcomap] at hloc
    exact hloc.symm
  have hzero : ∀ x : RK, x ∈ Q → φ x = 0 := by
    intro x hx
    exact (RingHom.mem_ker).mp (hker.symm ▸ hx)
  let φbar : RK ⧸ Q →ₐ[K] L :=
    Ideal.Quotient.liftₐ Q φ hzero
  have hφbar : Function.Injective φbar := by
    change Function.Injective
      (Ideal.Quotient.lift Q φ.toRingHom hzero)
    exact (Ideal.injective_lift_iff hzero).mpr hker
  letI : Algebra.IsAlgebraic K (RK ⧸ Q) :=
    Algebra.IsAlgebraic.of_injective φbar hφbar
  exact trdeg_eq_zero

/-! ## The canonical coefficient contraction and fibre prime -/

/-- The prime in `(A / p)[Y]` obtained from `P ⊂ A[Y]`, where
`p = P ∩ A`.  We first quotient by `p A[Y]` and then use the canonical
coefficient-quotient polynomial equivalence. -/
def polynomialFibreIdeal {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) :
    Ideal (MvPolynomial τ (A ⧸ coefficientContraction P)) :=
  let p := coefficientContraction P
  Ideal.map
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p).symm.toRingEquiv
    (P.map (Ideal.Quotient.mk
      (p.map (MvPolynomial.C : A →+* MvPolynomial τ A))))

/-- A prime polynomial ideal has prime coefficient contraction. -/
theorem coefficientContraction_isPrime
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (coefficientContraction P).IsPrime := by
  exact Ideal.comap_isPrime
    (f := (MvPolynomial.C : A →+* MvPolynomial τ A)) (K := P)

/-- The canonical fibre ideal of a prime is prime. -/
theorem polynomialFibreIdeal_isPrime
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (polynomialFibreIdeal P).IsPrime := by
  let p := coefficientContraction P
  letI : p.IsPrime := coefficientContraction_isPrime P
  have hpP : p.map
      (MvPolynomial.C : A →+* MvPolynomial τ A) ≤ P := by
    exact Ideal.map_comap_le
  let q : Ideal
      (MvPolynomial τ A ⧸
        p.map (MvPolynomial.C : A →+* MvPolynomial τ A)) :=
    P.map (Ideal.Quotient.mk
      (p.map (MvPolynomial.C : A →+* MvPolynomial τ A)))
  letI : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpP
  change (Ideal.map
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p).symm.toRingEquiv
    q).IsPrime
  infer_instance

/-- The canonical fibre prime contracts to zero in the coefficient-domain
quotient. -/
theorem polynomialFibreIdeal_comap_C
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    (polynomialFibreIdeal P).comap
      (MvPolynomial.C :
        (A ⧸ coefficientContraction P) →+*
          MvPolynomial τ (A ⧸ coefficientContraction P)) = ⊥ := by
  let p := coefficientContraction P
  let J : Ideal (MvPolynomial τ A) :=
    p.map (MvPolynomial.C : A →+* MvPolynomial τ A)
  have hJP : J ≤ P := by
    exact Ideal.map_comap_le
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  let q : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_bot]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change MvPolynomial.C (Ideal.Quotient.mk p a) ∈
      Ideal.map E.symm.toRingEquiv q at ha
    rw [Ideal.mem_map_iff_of_surjective E.symm.toRingEquiv
      E.symm.surjective] at ha
    obtain ⟨z, hz, hza⟩ := ha
    have heq : E (MvPolynomial.C (Ideal.Quotient.mk p a)) = z := by
      calc
        E (MvPolynomial.C (Ideal.Quotient.mk p a)) = E (E.symm z) :=
          congrArg E hza.symm
        _ = z := E.apply_symm_apply z
    have hz' : E (MvPolynomial.C (Ideal.Quotient.mk p a)) ∈ q := by
      rw [heq]
      exact hz
    have hE : E (MvPolynomial.C (Ideal.Quotient.mk p a)) =
        Ideal.Quotient.mk J (MvPolynomial.C a) := by
      simp [E, J, MvPolynomial.quotientEquivQuotientMvPolynomial]
    rw [hE, Ideal.mem_quotient_iff_mem hJP] at hz'
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hz'
  · exact bot_le

/-- A prime whose quotient is algebraic over a field is maximal.

This is the zero-dimensional endpoint used after passing to the fraction
field of a chosen transcendence basis.  Over a field, algebraicity is
integrality; lying over the maximal zero ideal then makes the zero ideal of
the quotient maximal.
-/
theorem prime_isMaximal_of_quotient_isAlgebraic
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (P : Ideal R) [P.IsPrime] [Algebra.IsAlgebraic K (R ⧸ P)] :
    P.IsMaximal := by
  rw [← Ideal.bot_quotient_isMaximal_iff P]
  letI : Algebra.IsIntegral K (R ⧸ P) :=
    Algebra.IsAlgebraic.isIntegral
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (R := K) (S := R ⧸ P) (⊥ : Ideal (R ⧸ P))
  simpa using (Ideal.bot_isMaximal (K := K))

/-- Every maximal ideal of a polynomial ring in finitely many variables over
a field has height equal to the number of variables.

The proof peels off one variable at a time.  The contraction of a maximal
ideal remains maximal because the coefficient ring is Jacobson, and
`Polynomial.height_eq_height_add_one` supplies the exact height increment.
-/
theorem maximalIdeal_height_eq_natCard
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsMaximal] :
    P.height = (Nat.card ι : ℕ∞) := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e IH =>
      let E : MvPolynomial β k ≃ₐ[k] MvPolynomial α k :=
        MvPolynomial.renameEquiv k e.symm
      let Q : Ideal (MvPolynomial α k) := Ideal.map E.toRingEquiv P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E.toRingEquiv
      calc
        P.height = Q.height := (E.toRingEquiv.height_map P).symm
        _ = (Nat.card α : ℕ∞) := IH Q
        _ = (Nat.card β : ℕ∞) := by rw [Nat.card_congr e]
  | h_empty =>
      let E : MvPolynomial PEmpty k ≃+* k :=
        MvPolynomial.isEmptyRingEquiv k PEmpty
      let Q : Ideal k := Ideal.map E P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E
      have hQ : Q = ⊥ := Ideal.eq_bot_of_prime Q
      calc
        P.height = Q.height := (E.height_map P).symm
        _ = (0 : ℕ∞) := by rw [hQ, Ideal.height_bot]
        _ = (Nat.card PEmpty : ℕ∞) := by simp
  | @h_option α _ IH =>
      let E : MvPolynomial (Option α) k ≃ₐ[k]
          Polynomial (MvPolynomial α k) :=
        MvPolynomial.optionEquivLeft k α
      let Q : Ideal (Polynomial (MvPolynomial α k)) :=
        Ideal.map E.toRingEquiv P
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv E.toRingEquiv
      let p : Ideal (MvPolynomial α k) := Q.comap Polynomial.C
      letI : p.IsMaximal :=
        Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
      letI : Q.LiesOver p := ⟨rfl⟩
      calc
        P.height = Q.height := (E.toRingEquiv.height_map P).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p Q
        _ = (Nat.card α : ℕ∞) + 1 := by rw [IH p]
        _ = (Nat.card (Option α) : ℕ∞) := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_option,
            Nat.cast_add, Nat.cast_one]

/-! ## The fraction-field height bridge -/

/-- Let `P` be a prime of `A[Y]`, where `A` is itself a finite polynomial
ring over a field.  Suppose that `P` contracts to zero in `A`.  After
localizing `A` to its fraction field `K`, if the quotient by the extended
prime has transcendence degree zero over `K`, then `P` has height exactly the
number of `Y` variables.

This is the form of the affine dimension formula needed by the provenance
argument.  Its proof is short and structural:

* zero contraction makes `P` disjoint from all nonzero coefficients;
* localization therefore preserves its height;
* transcendence degree zero makes the localized quotient algebraic, hence
  the extended prime maximal;
* the preceding closed-point theorem computes its height.

No catenarity or global prime-height formula is used as an assumption.
-/
theorem iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero
    {A τ : Type*} [CommRing A] [IsDomain A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime]
    (hcontract :
      P.comap (MvPolynomial.C :
        A →+* MvPolynomial τ A) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing A)
        (MvPolynomial τ (FractionRing A) ⧸
          P.map (MvPolynomial.map
            (algebraMap A (FractionRing A)))) = 0) :
    P.height = (Nat.card τ : ℕ∞) := by
  letI : Algebra
      (MvPolynomial τ A)
      (MvPolynomial τ (FractionRing A)) :=
    MvPolynomial.algebraMvPolynomial
  let M : Submonoid (MvPolynomial τ A) :=
    (nonZeroDivisors A).map
      (MvPolynomial.C :
        A →+* MvPolynomial τ A)
  let Q : Ideal (MvPolynomial τ (FractionRing A)) :=
    P.map (MvPolynomial.map
      (algebraMap A (FractionRing A)))
  have hdisj : Disjoint
      (M : Set (MvPolynomial τ A))
      (P : Set (MvPolynomial τ A)) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ hxP
    have haP : a ∈ P.comap
        (MvPolynomial.C :
          A →+* MvPolynomial τ A) := hxP
    rw [hcontract] at haP
    have ha0 : a = 0 := Ideal.mem_bot.mp haP
    subst a
    exact zero_notMem_nonZeroDivisors ha
  letI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M
      (MvPolynomial τ (FractionRing A)) P inferInstance hdisj
  letI : Algebra.IsAlgebraic
      (FractionRing A)
      (MvPolynomial τ (FractionRing A) ⧸ Q) :=
    trdeg_eq_zero_iff.mp htrdeg
  letI : Q.IsMaximal :=
    prime_isMaximal_of_quotient_isAlgebraic
      (K := FractionRing A) Q
  calc
    P.height = Q.height :=
      (IsLocalization.height_map_of_disjoint M P hdisj).symm
    _ = (Nat.card τ : ℕ∞) := maximalIdeal_height_eq_natCard Q

/-! ## The unconditional finite polynomial-prime dimension formula -/

/-- If a chosen set of quotient coordinates is a transcendence basis, then
the height of the prime is exactly the number of complementary coordinates.
The generic-fibre algebraicity required by the height bridge is proved above,
not supplied as a premise. -/
theorem prime_height_eq_complementCard_of_coordinateBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] (S : Set ι)
    (hS : IsTranscendenceBasis k
      (fun i : S ↦ quotientCoordinate P i)) :
    P.height = (Nat.card (Sᶜ : Set ι) : ℕ∞) := by
  let E : MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k) ≃ₐ[k]
      MvPolynomial ι k := coordinateSplitEquiv S
  let J : Ideal
      (MvPolynomial (Sᶜ : Set ι) (MvPolynomial S k)) :=
    coordinateSplitPrime P S
  letI : J.IsPrime := coordinateSplitPrime_isPrime P S
  have hJ : J.height = (Nat.card (Sᶜ : Set ι) : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero J
      (coordinateSplitPrime_contraction_eq_bot P S hS.1)
      (coordinateSplitPrime_genericFibre_trdeg_eq_zero P S hS)
  have htransport : P.height = J.height := by
    calc
      P.height = (P.map E.symm.toRingEquiv).height :=
        (E.symm.toRingEquiv.height_map P).symm
      _ = J.height := by
        change (P.map E.symm.toRingEquiv).height =
          (P.comap E.toRingEquiv).height
        exact congrArg Ideal.height (Ideal.map_symm E.toRingEquiv)
  exact htransport.trans hJ

/-- The affine dimension formula for an arbitrary prime of a polynomial ring
in finitely many variables over a field.  The transcendence degree is taken
in the quotient function field; `Cardinal.toNat` is harmless here because a
coordinate transcendence basis is finite. -/
theorem polynomialPrime_height_add_fractionTrdeg_eq_natCard
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    P.height +
        ((Algebra.trdeg k
          (FractionRing (MvPolynomial ι k ⧸ P))).toNat : ℕ∞) =
      (Nat.card ι : ℕ∞) := by
  classical
  obtain ⟨S, hS⟩ := exists_coordinateIndex_transcendenceBasis P
  let B := MvPolynomial ι k ⧸ P
  let L := FractionRing B
  letI : Algebra.IsAlgebraic B L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hSL : IsTranscendenceBasis k
      ((algebraMap B L) ∘
        (fun i : S ↦ quotientCoordinate P i)) :=
    hS.algebraMap_comp
  have htrdegNat :
      (Algebra.trdeg k L).toNat = Nat.card S := by
    have hlift := hSL.lift_cardinalMk_eq_trdeg
    have hnat := congrArg Cardinal.toNat hlift
    simpa [Nat.card] using hnat.symm
  have hcardSum :
      Nat.card S + Nat.card (Sᶜ : Set ι) = Nat.card ι := by
    calc
      Nat.card S + Nat.card (Sᶜ : Set ι) =
          Nat.card (S ⊕ (Sᶜ : Set ι)) := by
        rw [Nat.card_sum]
      _ = Nat.card ι := Nat.card_congr (Equiv.Set.sumCompl S)
  rw [prime_height_eq_complementCard_of_coordinateBasis P S hS]
  change (Nat.card (Sᶜ : Set ι) : ℕ∞) +
      ((Algebra.trdeg k L).toNat : ℕ∞) = (Nat.card ι : ℕ∞)
  rw [htrdegNat, ← Nat.cast_add]
  exact_mod_cast (by simpa [add_comm] using hcardSum)

/-- Relative prime-height formula over an arbitrary noetherian coefficient
domain.  The only geometric input is that the canonical generic fibre has
transcendence degree zero. -/
theorem polynomialPrime_height_eq_contractionHeight_add_card_of_fibre_trdeg_zero
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime]
    (htrdeg :
      Algebra.trdeg
        (FractionRing (A ⧸ coefficientContraction P))
        (MvPolynomial τ
            (FractionRing (A ⧸ coefficientContraction P)) ⧸
          (polynomialFibreIdeal P).map
            (MvPolynomial.map
              (algebraMap
                (A ⧸ coefficientContraction P)
                (FractionRing (A ⧸ coefficientContraction P))))) = 0) :
    P.height =
      (coefficientContraction P).height + (Nat.card τ : ℕ∞) := by
  let p := coefficientContraction P
  letI : p.IsPrime := coefficientContraction_isPrime P
  let F := polynomialFibreIdeal P
  letI : F.IsPrime := polynomialFibreIdeal_isPrime P
  have hFheight : F.height = (Nat.card τ : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero F
      (polynomialFibreIdeal_comap_C P) htrdeg
  let J : Ideal (MvPolynomial τ A) :=
    p.map (MvPolynomial.C : A →+* MvPolynomial τ A)
  let q : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  letI : P.LiesOver p := ⟨rfl⟩
  have hsplit :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have htransport : q.height = F.height := by
    exact (E.symm.toRingEquiv.height_map q).symm
  calc
    P.height = p.height + q.height := by
      simpa [J, q] using hsplit
    _ = p.height + F.height := by rw [htransport]
    _ = p.height + (Nat.card τ : ℕ∞) := by rw [hFheight]

/-! ## A coordinate-transcendence-basis form -/

/-- Regard the right variables as coefficient variables and the left
variables as the remaining polynomial variables. -/
def splitPrimeIdeal {k τ σ : Type*} [CommRing k]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) :
    Ideal (MvPolynomial τ (MvPolynomial σ k)) :=
  P.map (MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv

/-- A split transport of a prime is prime. -/
theorem splitPrimeIdeal_isPrime
    {k τ σ : Type*} [CommRing k]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime] :
    (splitPrimeIdeal P).IsPrime := by
  unfold splitPrimeIdeal
  infer_instance

/-- Coordinate-basis height formula.  If the right-coordinate polynomial
ring injects into the quotient and the remaining generic fibre is algebraic,
then the height is the number of left coordinates. -/
theorem splitPrime_height_eq_leftCard_of_right_coordinate_basis
    {k τ σ : Type*} [Field k] [Finite τ] [Finite σ]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime]
    (hcontract :
      coefficientContraction (splitPrimeIdeal P) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing (MvPolynomial σ k))
        (MvPolynomial τ (FractionRing (MvPolynomial σ k)) ⧸
          (splitPrimeIdeal P).map
            (MvPolynomial.map
              (algebraMap (MvPolynomial σ k)
                (FractionRing (MvPolynomial σ k))))) = 0) :
    P.height = (Nat.card τ : ℕ∞) := by
  let Q := splitPrimeIdeal P
  letI : Q.IsPrime := splitPrimeIdeal_isPrime P
  have hQ : Q.height = (Nat.card τ : ℕ∞) :=
    iteratedPrime_height_eq_remainingCard_of_fraction_trdeg_zero
      Q hcontract htrdeg
  calc
    P.height = Q.height :=
      ((MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv.height_map P).symm
    _ = (Nat.card τ : ℕ∞) := hQ

/-- The same coordinate-basis theorem in the classical
`height + transcendence-degree = number of variables` shape, with the size
of the chosen right-coordinate basis standing for the transcendence degree.
-/
theorem splitPrime_height_add_rightCard_eq_totalCard
    {k τ σ : Type*} [Field k] [Finite τ] [Finite σ]
    (P : Ideal (MvPolynomial (τ ⊕ σ) k)) [P.IsPrime]
    (hcontract :
      coefficientContraction (splitPrimeIdeal P) = ⊥)
    (htrdeg :
      Algebra.trdeg (FractionRing (MvPolynomial σ k))
        (MvPolynomial τ (FractionRing (MvPolynomial σ k)) ⧸
          (splitPrimeIdeal P).map
            (MvPolynomial.map
              (algebraMap (MvPolynomial σ k)
                (FractionRing (MvPolynomial σ k))))) = 0) :
    P.height + (Nat.card σ : ℕ∞) =
      (Nat.card (τ ⊕ σ) : ℕ∞) := by
  rw [splitPrime_height_eq_leftCard_of_right_coordinate_basis
    P hcontract htrdeg]
  rw [Nat.card_sum, Nat.cast_add]

end

end PolynomialPrimeTrdegHeight

end RB31E2E
