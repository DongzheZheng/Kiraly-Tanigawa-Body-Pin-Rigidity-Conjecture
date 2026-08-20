import RB31EndToEnd.API.Algebra

/-! A consumer of the public algebraic-certificate facade and no other project facade. -/

open scoped BigOperators

namespace PublicAPISmoke.Algebra

example {σ : Type*} (P : MvPolynomial σ ℝ) (hP : P ≠ 0) :
    ∃ x : σ → ℝ, MvPolynomial.eval x P ≠ 0 :=
  RB31E2E.ComplexRealSpecialization.exists_real_eval_ne_zero P hP

example {L K I C J : Type*}
    [Field L] [Field K] [Algebra L K]
    [Fintype I] [DecidableEq I] [Fintype C]
    (rows : J → I → L)
    (x : C → K) (hx : AlgebraicIndependent L x)
    (constant : I → L) (coefficient : C → I → L)
    (hmem :
      RB31E2E.FiniteFamilyBaseChange.mapVector (K := K) constant +
          ∑ j : C, x j •
            RB31E2E.FiniteFamilyBaseChange.mapVector
              (K := K) (coefficient j) ∈
        Submodule.span K (Set.range (fun r ↦
          RB31E2E.FiniteFamilyBaseChange.mapVector
            (K := K) (rows r)))) :
    constant ∈ Submodule.span L (Set.range rows) ∧
      ∀ j, coefficient j ∈ Submodule.span L (Set.range rows) :=
  RB31E2E.AffineSpanDescent.affineCoefficients_mem_span
    rows x hx constant coefficient hmem

example {k K Old New : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype New]
    (old : Old → K) (new : New → K)
    (hgen : IntermediateField.adjoin k
      (Set.range old ∪ Set.range new) = ⊤) :
    Algebra.trdeg k
          (RB31E2E.CoordinateFieldTower.oldCoordinateField
            (k := k) (K := K) old) +
        Algebra.trdeg
            (RB31E2E.CoordinateFieldTower.oldCoordinateField
              (k := k) (K := K) old) K =
          Algebra.trdeg k K ∧
      Algebra.trdeg
          (RB31E2E.CoordinateFieldTower.oldCoordinateField
            (k := k) (K := K) old) K ≤
        (Fintype.card New : Cardinal) :=
  RB31E2E.CoordinateFieldTower.trdeg_deletion_ledger
    (k := k) old new hgen

example { σ m n : Type* } [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (MvPolynomial σ ℤ))
    (hComplex : ∃ z : σ → ℂ,
      Function.Injective
        (RB31E2E.ComplexRealSpecialization.specializeMatrix
          (Int.castRingHom ℂ) z A).mulVec) :
    ∃ x : σ → ℝ,
      Function.Injective
        (RB31E2E.ComplexRealSpecialization.specializeMatrix
          (Int.castRingHom ℝ) x A).mulVec :=
  RB31E2E.ComplexRealSpecialization.exists_real_specialization_injective_of_complex
    A hComplex

example { ι σ : Type* } [Fintype ι]
    (Bad : (σ → ℝ) → Prop)
    (Chart : ι → (σ → ℝ) → Prop)
    (certificate : ι → MvPolynomial σ ℤ)
    (hNonzero : ∀ i, certificate i ≠ 0)
    (hCover : ∀ z, Bad z → ∃ i, Chart i z)
    (hChartVanish : ∀ i z, Chart i z →
      MvPolynomial.eval₂ (Int.castRingHom ℝ) z (certificate i) = 0) :
    ∃ P : MvPolynomial σ ℤ, P ≠ 0 ∧
      ∀ z, Bad z →
        MvPolynomial.eval₂ (Int.castRingHom ℝ) z P = 0 :=
  RB31E2E.FiniteChartCertificates.exists_uniform_certificate_of_finite_chart_cover
    Bad Chart certificate hNonzero hCover hChartVanish

example {k ι : Type*} [Field k]
    (p : Ideal (MvPolynomial ι k)) [p.IsPrime] :
    IntermediateField.adjoin k
      (Set.range (RB31E2E.FractionQuotientCoordinates.coordinate p)) = ⊤ :=
  RB31E2E.FractionQuotientCoordinates.adjoin_coordinate_eq_top p

example {σ ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (hP : ∀ i, P i ≠ 0) :
    ∃ (Q : MvPolynomial σ ℤ) (c : ℚ),
      Q ≠ 0 ∧ c ≠ 0 ∧
        MvPolynomial.map (Int.castRingHom ℚ) Q =
          MvPolynomial.C c * ∏ i, P i ∧
        ∀ i z,
          MvPolynomial.eval₂ (Rat.castHom ℝ) z (P i) = 0 →
            MvPolynomial.eval₂ (Int.castRingHom ℝ) z Q = 0 :=
  RB31E2E.RationalCertificateDescent.exists_integer_product_certificate P hP

end PublicAPISmoke.Algebra
