import RB31EndToEnd.Algebra.FiniteOpenIntersection

/-!
# Finite chart certificates

A pointwise algebraic-dependence argument does not by itself produce one
polynomial cutting out an entire bad locus.  This file records the finite
uniformity step explicitly.  If finitely many charts cover a bad predicate
and each chart has its own nonzero polynomial certificate, their product is
one nonzero certificate for the whole predicate.

The theorem is deliberately stated for actual evaluations.  Thus every use
must supply both finite chart coverage and a polynomial fixed uniformly on
each chart; a point-dependent witness cannot be smuggled through the API.
-/

namespace RB31E2E

namespace FiniteChartCertificates

noncomputable section

open MvPolynomial

variable {ι σ : Type*} [Fintype ι]

/-- The product of a finite family of integer polynomial certificates. -/
def combinedCertificate
    (certificate : ι → MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∏ i : ι, certificate i

/-- A finite product of nonzero integer multivariate polynomials is nonzero. -/
theorem combinedCertificate_ne_zero
    (certificate : ι → MvPolynomial σ ℤ)
    (hNonzero : ∀ i, certificate i ≠ 0) :
    combinedCertificate certificate ≠ 0 := by
  classical
  unfold combinedCertificate
  exact Finset.prod_ne_zero_iff.mpr fun i _hi ↦ hNonzero i

/-- If a point belongs to one certified chart, the combined certificate
vanishes at that point. -/
theorem eval₂_combinedCertificate_eq_zero_of_chart
    (certificate : ι → MvPolynomial σ ℤ)
    (z : σ → ℝ) (i : ι)
    (hi : eval₂ (Int.castRingHom ℝ) z (certificate i) = 0) :
    eval₂ (Int.castRingHom ℝ) z
        (combinedCertificate certificate) = 0 := by
  classical
  rw [combinedCertificate]
  change (eval₂Hom (Int.castRingHom ℝ) z)
      (∏ i, certificate i) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- Finite chart assembly with an explicit coverage predicate.  The
certificate attached to a chart is fixed before the bad point is chosen. -/
theorem combinedCertificate_vanishes_on_finite_cover
    (Bad : (σ → ℝ) → Prop) (Chart : ι → (σ → ℝ) → Prop)
    (certificate : ι → MvPolynomial σ ℤ)
    (hCover : ∀ z, Bad z → ∃ i, Chart i z)
    (hChartVanish : ∀ i z, Chart i z →
      eval₂ (Int.castRingHom ℝ) z (certificate i) = 0) :
    ∀ z, Bad z →
      eval₂ (Int.castRingHom ℝ) z
        (combinedCertificate certificate) = 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := hCover z hz
  exact eval₂_combinedCertificate_eq_zero_of_chart certificate z i
    (hChartVanish i z hi)

/-- A complete finite packet: fixed nonzero chart polynomials plus coverage
gives one fixed nonzero polynomial vanishing on the whole bad predicate. -/
theorem exists_uniform_certificate_of_finite_chart_cover
    (Bad : (σ → ℝ) → Prop) (Chart : ι → (σ → ℝ) → Prop)
    (certificate : ι → MvPolynomial σ ℤ)
    (hNonzero : ∀ i, certificate i ≠ 0)
    (hCover : ∀ z, Bad z → ∃ i, Chart i z)
    (hChartVanish : ∀ i z, Chart i z →
      eval₂ (Int.castRingHom ℝ) z (certificate i) = 0) :
    ∃ P : MvPolynomial σ ℤ, P ≠ 0 ∧
      ∀ z, Bad z → eval₂ (Int.castRingHom ℝ) z P = 0 := by
  refine ⟨combinedCertificate certificate,
    combinedCertificate_ne_zero certificate hNonzero, ?_⟩
  exact combinedCertificate_vanishes_on_finite_cover
    Bad Chart certificate hCover hChartVanish

end

end FiniteChartCertificates

end RB31E2E
