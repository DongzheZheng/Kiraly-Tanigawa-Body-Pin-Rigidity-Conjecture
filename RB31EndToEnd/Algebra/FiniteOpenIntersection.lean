import RB31EndToEnd.Algebra.ComplexRealSpecialization

/-!
# Finite intersections of principal real Zariski opens

For the end-to-end bridges we repeatedly have one full-rank minor and
finitely many nondegeneracy/distinctness polynomials.  Their principal open
sets meet because the product polynomial is nonzero.  This elementary file
keeps that step independent of scheme topology.
-/

namespace RB31E2E

namespace ComplexRealSpecialization

open MvPolynomial

theorem exists_real_eval_ne_zero_all {σ : Type*}
    (S : Finset (MvPolynomial σ ℝ))
    (hS : ∀ P ∈ S, P ≠ 0) :
    ∃ x : σ → ℝ, ∀ P ∈ S, eval x P ≠ 0 := by
  classical
  have hprod : ∏ P ∈ S, P ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun P hP ↦ hS P hP
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero (∏ P ∈ S, P) hprod
  refine ⟨x, ?_⟩
  intro P hP hzero
  apply hx
  simp only [map_prod]
  exact Finset.prod_eq_zero hP hzero

theorem exists_real_eval₂_ne_zero_all_int {σ : Type*}
    (S : Finset (MvPolynomial σ ℤ))
    (hS : ∀ P ∈ S, P ≠ 0) :
    ∃ x : σ → ℝ, ∀ P ∈ S,
      eval₂ (Int.castRingHom ℝ) x P ≠ 0 := by
  classical
  let Sreal : Finset (MvPolynomial σ ℝ) :=
    S.image (MvPolynomial.map (Int.castRingHom ℝ))
  have hSreal : ∀ P ∈ Sreal, P ≠ 0 := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨Q, hQS, rfl⟩
    exact (MvPolynomial.map_injective (Int.castRingHom ℝ)
      Int.cast_injective).ne (hS Q hQS)
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero_all Sreal hSreal
  refine ⟨x, fun P hP ↦ ?_⟩
  have hmem : MvPolynomial.map (Int.castRingHom ℝ) P ∈ Sreal :=
    Finset.mem_image.mpr ⟨P, hP, rfl⟩
  simpa only [eval_map] using hx _ hmem

end ComplexRealSpecialization

end RB31E2E
