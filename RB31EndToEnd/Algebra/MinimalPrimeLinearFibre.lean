import RB31EndToEnd.Algebra.PolynomialPrimeTrdegHeight
import RB31EndToEnd.Algebra.LinearFormIdeal
import RB31EndToEnd.Incidence.ActivePinPrimeHeight
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Minimal primes in a coefficient generic fibre

Given a minimal prime `P` above an ideal in `A[Y]`, contract `P` to the
coefficient ring, quotient by that contraction, and then pass to its fraction
field.  This file proves that the resulting prime remains minimal above the
image of the original ideal.  Consequently, if the generic-fibre equations
are visibly a linear-form prime lying below the image of `P`, minimality
identifies the two ideals.

The quotient and localization steps are both explicit; no generic-fibre
minimality or equidimensionality statement is assumed.
-/

namespace RB31E2E

namespace MinimalPrimeLinearFibre

noncomputable section

open MvPolynomial
open PolynomialPrimeTrdegHeight
open ActivePinPrimeHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The coefficient-quotient map on a polynomial ring. -/
abbrev coefficientQuotientMap
    {A τ : Type*} [CommRing A] (p : Ideal A) :
    MvPolynomial τ A →+* MvPolynomial τ (A ⧸ p) :=
  quotientCoefficientMap (P := p) ( σ := τ)

/-- The image of a prime under coefficient quotient has zero coefficient
contraction when the quotient ideal is exactly its coefficient contraction. -/
theorem coefficientQuotient_prime_comap_C_eq_bot
    {A τ : Type*} [CommRing A]
    (P : Ideal (MvPolynomial τ A)) [P.IsPrime] :
    let p := coefficientContraction P
    let q := coefficientQuotientMap ( τ := τ) p
    (Ideal.map q P).comap
      (C : (A ⧸ p) →+* MvPolynomial τ (A ⧸ p)) = ⊥ := by
  classical
  dsimp only
  let p := coefficientContraction P
  let q := coefficientQuotientMap ( τ := τ) p
  have hqSurj : Function.Surjective q :=
    quotientCoefficientMap_surjective (P := p) ( σ := τ)
  have hker : RingHom.ker q ≤ P := by
    rw [quotientCoefficientMap_ker]
    exact Ideal.map_comap_le
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_bot]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : C (Ideal.Quotient.mk p a) ∈ Ideal.map q P := hb
    rw [Ideal.mem_map_iff_of_surjective q hqSurj] at hb'
    obtain ⟨z, hzP, hz⟩ := hb'
    have hdiff : z - C a ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_sub, hz]
      simp [q, quotientCoefficientMap]
    have hCa : C a ∈ P := by
      have hzsub : z - (z - C a) ∈ P := P.sub_mem hzP (hker hdiff)
      simpa only [sub_sub_cancel] using hzsub
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hCa
  · exact bot_le

/-- A minimal prime remains minimal after quotienting by its own coefficient
contraction. -/
theorem coefficientQuotient_map_mem_minimalPrimes
    {A τ : Type*} [CommRing A]
    (I P : Ideal (MvPolynomial τ A))
    (hP : P ∈ I.minimalPrimes) :
    let p := coefficientContraction P
    let q := coefficientQuotientMap ( τ := τ) p
    Ideal.map q P ∈ (Ideal.map q I).minimalPrimes := by
  classical
  dsimp only
  let p := coefficientContraction P
  let q := coefficientQuotientMap ( τ := τ) p
  have hqSurj : Function.Surjective q :=
    quotientCoefficientMap_surjective (P := p) ( σ := τ)
  have hkerP : RingHom.ker q ≤ P := by
    rw [quotientCoefficientMap_ker]
    exact Ideal.map_comap_le
  have hPjoin : P ∈ (I ⊔ RingHom.ker q).minimalPrimes := by
    refine ⟨⟨hP.1.1, sup_le hP.1.2 hkerP⟩, ?_⟩
    intro Q hQ hQP
    exact hP.2 ⟨hQ.1, le_sup_left.trans hQ.2⟩ hQP
  rw [Ideal.minimalPrimes_map_of_surjective hqSurj I]
  exact ⟨P, hPjoin, rfl⟩

/-- After quotienting the coefficient contraction and localizing the
coefficient domain to its fraction field, the image of `P` is still a
minimal prime above the image of `I`. -/
theorem fractionFibre_map_mem_minimalPrimes
    {A τ : Type*} [CommRing A]
    (I P : Ideal (MvPolynomial τ A))
    (hP : P ∈ I.minimalPrimes) :
    let p := coefficientContraction P
    let B := A ⧸ p
    let K := FractionRing B
    let q := coefficientQuotientMap ( τ := τ) p
    let ℓ := MvPolynomial.map (algebraMap B K)
    Ideal.map ℓ (Ideal.map q P) ∈
      (Ideal.map ℓ (Ideal.map q I)).minimalPrimes := by
  classical
  dsimp only
  let p := coefficientContraction P
  let B := A ⧸ p
  let K := FractionRing B
  let R := MvPolynomial τ B
  let RK := MvPolynomial τ K
  let q := coefficientQuotientMap ( τ := τ) p
  let ℓ : R →+* RK := MvPolynomial.map (algebraMap B K)
  letI : P.IsPrime := hP.1.1
  letI : p.IsPrime := coefficientContraction_isPrime P
  let M : Submonoid R :=
    (nonZeroDivisors B).map (C : B →+* R)
  have hPq := coefficientQuotient_map_mem_minimalPrimes I P hP
  let Pq : Ideal R := Ideal.map q P
  let Iq : Ideal R := Ideal.map q I
  have hPqPrime : Pq.IsPrime := hPq.1.1
  letI : Pq.IsPrime := hPqPrime
  have hcontract : Pq.comap (C : B →+* R) = ⊥ := by
    exact coefficientQuotient_prime_comap_C_eq_bot P
  have hdisj : Disjoint (M : Set R) (Pq : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨b, hb, rfl⟩ hx
    have hbP : b ∈ Pq.comap (C : B →+* R) := hx
    rw [hcontract] at hbP
    have hb0 : b = 0 := Ideal.mem_bot.mp hbP
    subst b
    exact zero_notMem_nonZeroDivisors hb
  have hPLPrime : (Ideal.map ℓ Pq).IsPrime := by
    change (Ideal.map (algebraMap R RK) Pq).IsPrime
    exact IsLocalization.isPrime_of_isPrime_disjoint M RK Pq
      (inferInstance : Pq.IsPrime) hdisj
  letI : (Ideal.map ℓ Pq).IsPrime := hPLPrime
  change Ideal.map (algebraMap R RK) Pq ∈
    (Ideal.map (algebraMap R RK) Iq).minimalPrimes
  rw [IsLocalization.minimalPrimes_map M RK Iq]
  change Ideal.comap (algebraMap R RK) (Ideal.map ℓ Pq) ∈
    Iq.minimalPrimes
  have hcomap :
      Ideal.comap (algebraMap R RK) (Ideal.map ℓ Pq) = Pq := by
    change Ideal.comap (algebraMap R RK)
      (Ideal.map (algebraMap R RK) Pq) = Pq
    exact IsLocalization.comap_map_of_isPrime_disjoint M RK
      (inferInstance : Pq.IsPrime) hdisj
  rw [hcomap]
  exact hPq

/-- Minimality identifies any prime linear-form ideal sandwiched between the
generic-fibre equations and the surviving generic-fibre component. -/
theorem linearFormIdeal_eq_fractionFibrePrime
    {A τ J : Type*} [CommRing A]
    [Fintype τ] [DecidableEq τ]
    (I P : Ideal (MvPolynomial τ A))
    [P.IsPrime]
    [(coefficientContraction P).IsPrime]
    (hP : P ∈ I.minimalPrimes)
    (row : J → τ → FractionRing (A ⧸ coefficientContraction P))
    (hI :
      Ideal.map
          (MvPolynomial.map
            (algebraMap (A ⧸ coefficientContraction P)
              (FractionRing (A ⧸ coefficientContraction P))))
          (Ideal.map
            (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) I) ≤
        LinearFormIdeal.linearFormIdeal row)
    (hPupper :
      LinearFormIdeal.linearFormIdeal row ≤
        Ideal.map
          (MvPolynomial.map
            (algebraMap (A ⧸ coefficientContraction P)
              (FractionRing (A ⧸ coefficientContraction P))))
          (Ideal.map
            (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P)) :
    LinearFormIdeal.linearFormIdeal row =
      Ideal.map
        (MvPolynomial.map
          (algebraMap (A ⧸ coefficientContraction P)
            (FractionRing (A ⧸ coefficientContraction P))))
        (Ideal.map
          (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P) := by
  let Q := LinearFormIdeal.linearFormIdeal row
  let PL := Ideal.map
    (MvPolynomial.map
      (algebraMap (A ⧸ coefficientContraction P)
        (FractionRing (A ⧸ coefficientContraction P))))
    (Ideal.map
      (coefficientQuotientMap ( τ := τ) (coefficientContraction P)) P)
  have hmin := fractionFibre_map_mem_minimalPrimes I P hP
  have hQPrime : Q.IsPrime := LinearFormIdeal.linearFormIdeal_isPrime row
  exact le_antisymm hPupper (hmin.2 ⟨hQPrime, hI⟩ hPupper)

end

end MinimalPrimeLinearFibre

end RB31E2E
