import RB31EndToEnd.Algebra.MinimalPrimeLinearFibre

/-!
# Relative height through the coefficient generic fibre

For a prime in `A[Y]`, height splits into the height of its coefficient
contraction and the height of its prime generic fibre.  This is proved by
the canonical coefficient quotient and localization; no dimension formula
is assumed.
-/

namespace RB31E2E

namespace MinimalPrimeLinearFibre

noncomputable section

open MvPolynomial
open PolynomialPrimeTrdegHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The direct coefficient-quotient image used in this namespace is the
canonical polynomial fibre ideal. -/
theorem coefficientQuotient_map_eq_polynomialFibreIdeal
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) :
    Ideal.map
        (coefficientQuotientMap (τ := τ) (coefficientContraction P)) P =
      polynomialFibreIdeal P := by
  classical
  let p := coefficientContraction P
  let J : Ideal (MvPolynomial τ A) :=
    p.map (C : A →+* MvPolynomial τ A)
  let E : MvPolynomial τ (A ⧸ p) ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  have hhom :
      E.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J) =
        coefficientQuotientMap (τ := τ) p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, J, coefficientQuotientMap,
        ActivePinPrimeHeight.quotientCoefficientMap,
        MvPolynomial.quotientEquivQuotientMvPolynomial]
    · intro i
      simp [E, J, coefficientQuotientMap,
        ActivePinPrimeHeight.quotientCoefficientMap,
        MvPolynomial.quotientEquivQuotientMvPolynomial]
  change Ideal.map (coefficientQuotientMap (τ := τ) p) P =
    Ideal.map E.symm.toRingEquiv
      (Ideal.map (Ideal.Quotient.mk J) P)
  calc
    Ideal.map (coefficientQuotientMap (τ := τ) p) P =
        Ideal.map
          (E.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J)) P :=
      congrArg (fun f ↦ Ideal.map f P) hhom.symm
    _ = Ideal.map E.symm.toRingEquiv
        (Ideal.map (Ideal.Quotient.mk J) P) := by
      exact (Ideal.map_map (Ideal.Quotient.mk J)
        E.symm.toRingEquiv.toRingHom).symm

/-- Exact prime-height decomposition into coefficient contraction and
localized generic-fibre height. -/
theorem polynomialPrime_height_eq_contractionHeight_add_fractionFibreHeight
    {A τ : Type*} [CommRing A] [IsNoetherianRing A] [Finite τ]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    let p := coefficientContraction P
    let B := A ⧸ p
    let K := FractionRing B
    let q := coefficientQuotientMap (τ := τ) p
    let ℓ := MvPolynomial.map (algebraMap B K)
    P.height = p.height +
      (Ideal.map ℓ (Ideal.map q P)).height := by
  classical
  dsimp only
  let p := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let R := MvPolynomial τ B
  let RK := MvPolynomial τ K
  let q := coefficientQuotientMap (τ := τ) p
  let ℓ : R →+* RK := MvPolynomial.map (algebraMap B K)
  let Pq : Ideal R := Ideal.map q P
  let PL : Ideal RK := Ideal.map ℓ Pq
  letI : p.IsPrime := coefficientContraction_isPrime P
  have hPqF : Pq = polynomialFibreIdeal P := by
    exact coefficientQuotient_map_eq_polynomialFibreIdeal P
  have hPqPrime : Pq.IsPrime := by
    rw [hPqF]
    exact polynomialFibreIdeal_isPrime P
  letI : Pq.IsPrime := hPqPrime
  have hcontract : Pq.comap (C : B →+* R) = ⊥ := by
    exact coefficientQuotient_prime_comap_C_eq_bot P
  let M : Submonoid R :=
    (nonZeroDivisors B).map (C : B →+* R)
  have hdisj : Disjoint (M : Set R) (Pq : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨b, hb, rfl⟩ hx
    have hbP : b ∈ Pq.comap (C : B →+* R) := hx
    rw [hcontract] at hbP
    have hb0 : b = 0 := Ideal.mem_bot.mp hbP
    subst b
    exact zero_notMem_nonZeroDivisors hb
  have hlocal : PL.height = Pq.height := by
    change (Ideal.map (algebraMap R RK) Pq).height = Pq.height
    exact IsLocalization.height_map_of_disjoint M Pq hdisj
  let J : Ideal (MvPolynomial τ A) :=
    p.map (C : A →+* MvPolynomial τ A)
  let qabs : Ideal (MvPolynomial τ A ⧸ J) :=
    P.map (Ideal.Quotient.mk J)
  let E : MvPolynomial τ B ≃ₐ[A]
      (MvPolynomial τ A ⧸ J) :=
    MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) p
  letI : P.LiesOver p := ⟨rfl⟩
  have hsplit :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have htransport : qabs.height = Pq.height := by
    calc
      qabs.height = (polynomialFibreIdeal P).height :=
        (E.symm.toRingEquiv.height_map qabs).symm
      _ = Pq.height := congrArg Ideal.height hPqF.symm
  calc
    P.height = p.height + qabs.height := by
      simpa [J, qabs] using hsplit
    _ = p.height + Pq.height := by rw [htransport]
    _ = p.height + PL.height := by rw [hlocal]

end

end MinimalPrimeLinearFibre

end RB31E2E
