import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic

/-!
# Descent of rational polynomial certificates to the integers

A polynomial over `ℚ` involves only finitely many coefficients, even when its
variable type is infinite.  This file packages denominator clearing in a form
suited to geometric bad-locus certificates: every nonzero rational polynomial
is proportional to the coefficient cast of a nonzero integer polynomial, and
therefore its real zero set is contained in the real zero set of that integer
polynomial.

The construction below is structural rather than coefficientwise.  At an
addition node the two already-cleared denominators are cross-multiplied; at a
variable node the denominator is unchanged.  Thus no finiteness hypothesis on
the variable type is needed.
-/

namespace RB31E2E

namespace RationalCertificateDescent

noncomputable section

open MvPolynomial

variable {σ : Type*}

/-- Every rational multivariate polynomial has an integer multiple represented
by an integer polynomial.  The multiplier is a nonzero natural number. -/
theorem exists_natCast_mul_eq_map (P : MvPolynomial σ ℚ) :
    ∃ (Q : MvPolynomial σ ℤ) (d : ℕ), d ≠ 0 ∧
      map (Int.castRingHom ℚ) Q = C (d : ℚ) * P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C a.num, a.den, a.den_ne_zero, ?_⟩
      rw [map_C, ← C_mul]
      have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
      have hnum : (a.num : ℚ) = a * (a.den : ℚ) :=
        (div_eq_iff hden).mp a.num_div_den
      apply congrArg (fun x : ℚ ↦ (C x : MvPolynomial σ ℚ))
      change (a.num : ℚ) = (a.den : ℚ) * a
      exact hnum.trans (mul_comm _ _)
  | add P R hP hR =>
      obtain ⟨Q, d, hd, hQ⟩ := hP
      obtain ⟨S, e, he, hS⟩ := hR
      refine ⟨C (e : ℤ) * Q + C (d : ℤ) * S, d * e,
        Nat.mul_ne_zero hd he, ?_⟩
      simp only [map_add, map_mul, map_C, hQ, hS, Nat.cast_mul]
      simp only [Int.coe_castRingHom, Int.cast_natCast]
      ring
  | mul_X P i hP =>
      obtain ⟨Q, d, hd, hQ⟩ := hP
      refine ⟨Q * X i, d, hd, ?_⟩
      simp only [map_mul, map_X, hQ]
      ring

/-- A nonzero rational polynomial admits a nonzero integer certificate whose
coefficient cast is a nonzero rational scalar multiple of the original
polynomial. -/
theorem exists_integer_proportional
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * P := by
  obtain ⟨Q, d, hd, hQ⟩ := exists_natCast_mul_eq_map P
  refine ⟨Q, (d : ℚ), ?_, Nat.cast_ne_zero.mpr hd, hQ⟩
  intro hQzero
  rw [hQzero, map_zero] at hQ
  have hc : C (d : ℚ) ≠ (0 : MvPolynomial σ ℚ) :=
    C_ne_zero.mpr (Nat.cast_ne_zero.mpr hd)
  exact hP (mul_eq_zero.mp hQ.symm |>.resolve_left hc)

/-- Evaluation commutes with the two-stage coefficient cast `ℤ → ℚ → ℝ`.
This small lemma keeps the zero-set theorem below independent of definitional
details of the canonical cast homomorphisms. -/
theorem eval₂_map_intCast_ratCast
    (Q : MvPolynomial σ ℤ) (z : σ → ℝ) :
    eval₂ (Rat.castHom ℝ) z (map (Int.castRingHom ℚ) Q) =
      eval₂ (Int.castRingHom ℝ) z Q := by
  rw [eval₂_map]
  congr 1

/-- If a rational polynomial vanishes at a real assignment, then every
integer certificate obtained from a proportionality equation vanishes there
as well. -/
theorem eval₂_integer_eq_zero_of_proportional
    {P : MvPolynomial σ ℚ} {Q : MvPolynomial σ ℤ} {c : ℚ}
    (hProportional : map (Int.castRingHom ℚ) Q = C c * P)
    (z : σ → ℝ)
    (hPzero : eval₂ (Rat.castHom ℝ) z P = 0) :
    eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  rw [← eval₂_map_intCast_ratCast Q z, hProportional]
  simp [hPzero]

/-- End-to-end one-polynomial descent packet: a nonzero rational certificate
produces a nonzero integer certificate and the latter vanishes at every real
zero of the former. -/
theorem exists_integer_certificate_vanishing_on_real_zeros
    (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * P ∧
        ∀ z : σ → ℝ,
          eval₂ (Rat.castHom ℝ) z P = 0 →
            eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  obtain ⟨Q, c, hQ, hc, hProportional⟩ :=
    exists_integer_proportional P hP
  exact ⟨Q, c, hQ, hc, hProportional,
    fun z hz ↦ eval₂_integer_eq_zero_of_proportional hProportional z hz⟩

/-- A finite family of nonzero rational certificates can be descended one by
one to nonzero integer certificates, with all real zero-set implications
retained. -/
theorem exists_integer_certificate_family
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (hP : ∀ i, P i ≠ 0) :
    ∃ (Q : ι → MvPolynomial σ ℤ) (c : ι → ℚ),
      (∀ i, Q i ≠ 0) ∧ (∀ i, c i ≠ 0) ∧
      (∀ i, map (Int.castRingHom ℚ) (Q i) = C (c i) * P i) ∧
      ∀ i z, eval₂ (Rat.castHom ℝ) z (P i) = 0 →
        eval₂ (Int.castRingHom ℝ) z (Q i) = 0 := by
  choose Q c hQ hc hProportional hVanish using
    fun i ↦ exists_integer_certificate_vanishing_on_real_zeros (P i) (hP i)
  exact ⟨Q, c, hQ, hc, hProportional, hVanish⟩

/-- Proportionality is preserved when finitely many descended certificates
are multiplied. -/
theorem map_product_eq_scalar_mul_product
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (Q : ι → MvPolynomial σ ℤ)
    (c : ι → ℚ)
    (hProportional : ∀ i,
      map (Int.castRingHom ℚ) (Q i) = C (c i) * P i) :
    map (Int.castRingHom ℚ) (∏ i, Q i) =
      C (∏ i, c i) * ∏ i, P i := by
  classical
  calc
    map (Int.castRingHom ℚ) (∏ i, Q i) =
        ∏ i, map (Int.castRingHom ℚ) (Q i) := by rw [map_prod]
    _ = ∏ i, (C (c i) * P i) :=
      Finset.prod_congr rfl fun i _hi ↦ hProportional i
    _ = (∏ i, C (c i)) * ∏ i, P i := Finset.prod_mul_distrib
    _ = C (∏ i, c i) * ∏ i, P i := by rw [map_prod]

/-- Finite-product descent packet.  It is the direct interface needed after
a finite chart/component split: the product integer certificate is nonzero,
is proportional to the product rational certificate, and vanishes whenever
one chosen rational factor vanishes. -/
theorem exists_integer_product_certificate
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (hP : ∀ i, P i ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        map (Int.castRingHom ℚ) Q = C c * ∏ i, P i ∧
        ∀ i z, eval₂ (Rat.castHom ℝ) z (P i) = 0 →
          eval₂ (Int.castRingHom ℝ) z Q = 0 := by
  classical
  obtain ⟨Q, c, hQ, hc, hProportional, hVanish⟩ :=
    exists_integer_certificate_family P hP
  refine ⟨∏ i, Q i, ∏ i, c i,
    Finset.prod_ne_zero_iff.mpr (fun i _hi ↦ hQ i),
    Finset.prod_ne_zero_iff.mpr (fun i _hi ↦ hc i),
    map_product_eq_scalar_mul_product P Q c hProportional, ?_⟩
  intro i z hz
  change (eval₂Hom (Int.castRingHom ℝ) z) (∏ i, Q i) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hVanish i z hz)

end

end RationalCertificateDescent

end RB31E2E
