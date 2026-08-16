import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Complex-to-real specialization for polynomial certificates

A nonzero polynomial over the reals has a real nonvanishing point.  Therefore
a polynomial certificate with coefficients in a ring that embeds into the
reals cannot exist only over the complexes.  The variable type need not be
finite: every multivariate polynomial has finite support, and
`MvPolynomial.funext` already packages that reduction.
-/

namespace RB31E2E

namespace ComplexRealSpecialization

open MvPolynomial

/-- A nonzero real multivariate polynomial is nonzero at some real point.
This is stronger than the finite-variable version: `σ` is arbitrary. -/
theorem exists_real_eval_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℝ) (hP : P ≠ 0) :
    ∃ x : σ → ℝ, eval x P ≠ 0 := by
  by_contra hnone
  apply hP
  apply MvPolynomial.funext
  intro x
  have hx : eval x P = 0 := by
    by_contra hx
    exact hnone ⟨x, hx⟩
  simpa using hx

/-- Generic coefficient bridge.  The complex coefficient map need not be
injective: one nonzero complex evaluation already proves that the source
polynomial is nonzero.  Only the coefficient map into `ℝ` must be injective. -/
theorem map_real_ne_zero_and_exists_eval_of_complex_eval
    {R σ : Type*} [CommSemiring R]
    (toComplex : R →+* ℂ) (toReal : R →+* ℝ)
    (htoReal : Function.Injective toReal)
    (P : MvPolynomial σ R)
    (hComplex : ∃ z : σ → ℂ, eval z (map toComplex P) ≠ 0) :
    map toReal P ≠ 0 ∧ ∃ x : σ → ℝ, eval x (map toReal P) ≠ 0 := by
  obtain ⟨z, hz⟩ := hComplex
  have hP : P ≠ 0 := by
    intro hzero
    subst P
    apply hz
    simp
  have hReal : map toReal P ≠ 0 := by
    simpa using (MvPolynomial.map_injective toReal htoReal).ne hP
  exact ⟨hReal, exists_real_eval_ne_zero (map toReal P) hReal⟩

/-- Integer-coefficient specialization bridge. -/
theorem int_real_nonvanishing_of_complex_nonvanishing
    {σ : Type*} (P : MvPolynomial σ ℤ)
    (hComplex : ∃ z : σ → ℂ,
      eval z (map (Int.castRingHom ℂ) P) ≠ 0) :
    map (Int.castRingHom ℝ) P ≠ 0 ∧
      ∃ x : σ → ℝ, eval x (map (Int.castRingHom ℝ) P) ≠ 0 :=
  map_real_ne_zero_and_exists_eval_of_complex_eval
    (Int.castRingHom ℂ) (Int.castRingHom ℝ) Int.cast_injective P hComplex

/-- Rational-coefficient specialization bridge. -/
theorem rat_real_nonvanishing_of_complex_nonvanishing
    {σ : Type*} (P : MvPolynomial σ ℚ)
    (hComplex : ∃ z : σ → ℂ,
      eval z (map (Rat.castHom ℂ) P) ≠ 0) :
    map (Rat.castHom ℝ) P ≠ 0 ∧
      ∃ x : σ → ℝ, eval x (map (Rat.castHom ℝ) P) ≠ 0 :=
  map_real_ne_zero_and_exists_eval_of_complex_eval
    (Rat.castHom ℂ) (Rat.castHom ℝ) Rat.cast_injective P hComplex

/-! ## Finite matrices -/

/-- Entrywise specialization of a polynomial matrix. -/
noncomputable def specializeMatrix
    {R S σ m n : Type*} [CommSemiring R] [CommSemiring S]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix m n (MvPolynomial σ R)) : Matrix m n S :=
  A.map (MvPolynomial.eval₂Hom coeff x)

@[simp]
theorem specializeMatrix_apply
    {R S σ m n : Type*} [CommSemiring R] [CommSemiring S]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix m n (MvPolynomial σ R)) (i : m) (j : n) :
    specializeMatrix coeff x A i j = eval₂ coeff x (A i j) :=
  rfl

/-- Determinants commute with entrywise polynomial specialization. -/
theorem det_specializeMatrix
    {R S σ n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix n n (MvPolynomial σ R)) :
    (specializeMatrix coeff x A).det = eval₂ coeff x A.det := by
  simpa [specializeMatrix] using
    (RingHom.map_det (MvPolynomial.eval₂Hom coeff x) A).symm

/-- A square matrix over a field with nonzero determinant acts injectively on
column vectors. -/
theorem mulVec_injective_of_det_ne_zero
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hdet : A.det ≠ 0) :
    Function.Injective A.mulVec := by
  intro v w hvw
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  rw [Matrix.mulVec_sub, hvw, sub_self]

/-- An injective finite matrix over a field has a nonzero full-column minor.
This is the elementary row-basis extraction needed before applying a
determinant polynomial certificate. -/
theorem exists_fullColumnMinor_of_mulVec_injective
    {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n K) (hA : Function.Injective A.mulVec) :
    ∃ rows : n → m, (A.submatrix rows id).det ≠ 0 := by
  classical
  have hLin : Function.Injective A.mulVecLin := by
    intro v w hvw
    apply hA
    simpa only [Matrix.mulVecLin_apply] using hvw
  have hRank : A.rank = Fintype.card n := by
    have hNullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [LinearMap.ker_eq_bot.mpr hLin, finrank_bot, add_zero,
      Module.finrank_fintype_fun_eq_card] at hNullity
    exact hNullity
  have hFinrankRows :
      Module.finrank K (Submodule.span K (Set.range A.row)) = Fintype.card n := by
    rw [← Matrix.rank_eq_finrank_span_row A]
    exact hRank
  have hSpanRows : Submodule.span K (Set.range A.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq <| by
      rw [hFinrankRows, Module.finrank_fintype_fun_eq_card]
  have hSelect :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  rw [hFinrankRows] at hSelect
  obtain ⟨f, hfMem, _, hfIndependent⟩ := hSelect
  have hfRows : ∀ i, ∃ r : m, A.row r = f i := fun i ↦ hfMem i
  choose selected hSelected using hfRows
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let rows : n → m := fun i ↦ selected (e i)
  have hRowsIndependent :
      LinearIndependent K (A.submatrix rows id).row := by
    have hRowEq : (A.submatrix rows id).row = f ∘ e := by
      funext i j
      change A (selected (e i)) j = f (e i) j
      exact congrFun (hSelected (e i)) j
    rw [hRowEq]
    exact hfIndependent.comp e e.injective
  have hUnitMatrix : IsUnit (A.submatrix rows id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hRowsIndependent
  have hUnitDet : IsUnit (A.submatrix rows id).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hUnitMatrix
  exact ⟨rows, isUnit_iff_ne_zero.mp hUnitDet⟩

/-- For a square integer-coefficient polynomial matrix, injectivity at one
complex specialization implies injectivity at some real specialization.
No degree bound on the entries is needed. -/
theorem exists_real_specialization_injective_of_complex_square
    {σ n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ ℤ))
    (hComplex : ∃ z : σ → ℂ,
      Function.Injective (specializeMatrix (Int.castRingHom ℂ) z A).mulVec) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  obtain ⟨z, hz⟩ := hComplex
  have hdetComplex : (specializeMatrix (Int.castRingHom ℂ) z A).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hvzero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M :=
        specializeMatrix (Int.castRingHom ℂ) z A)).mpr hdet
    apply hv
    apply hz
    simpa using hvzero
  have hPolynomialComplex : ∃ z : σ → ℂ,
      eval z (map (Int.castRingHom ℂ) A.det) ≠ 0 := by
    refine ⟨z, ?_⟩
    rw [eval_map, ← det_specializeMatrix]
    exact hdetComplex
  obtain ⟨_, x, hx⟩ :=
    int_real_nonvanishing_of_complex_nonvanishing A.det hPolynomialComplex
  refine ⟨x, mulVec_injective_of_det_ne_zero _ ?_⟩
  rw [det_specializeMatrix]
  simpa only [eval_map] using hx

/-- Rectangular full-column-rank bridge from a certified nonzero complex
full-column minor.  The row selector `rows` need not be assumed injective: a
nonzero determinant already forces the selected rows to be distinct enough.
The conclusion is injectivity of the entire real-specialized matrix. -/
theorem exists_real_specialization_injective_of_complex_minor
    {σ m n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n (MvPolynomial σ ℤ)) (rows : n → m)
    (hComplex : ∃ z : σ → ℂ,
      (specializeMatrix (Int.castRingHom ℂ) z
        (A.submatrix rows id)).det ≠ 0) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  have hMinorComplex : ∃ z : σ → ℂ,
      Function.Injective
        (specializeMatrix (Int.castRingHom ℂ) z
          (A.submatrix rows id)).mulVec := by
    obtain ⟨z, hz⟩ := hComplex
    exact ⟨z, mulVec_injective_of_det_ne_zero _ hz⟩
  obtain ⟨x, hMinorReal⟩ :=
    exists_real_specialization_injective_of_complex_square
      (A.submatrix rows id) hMinorComplex
  refine ⟨x, ?_⟩
  intro v w hvw
  apply hMinorReal
  funext i
  simpa [specializeMatrix, Matrix.mulVec] using congrFun hvw (rows i)

/-- Full rectangular form.  An injective complex specialization supplies a
nonzero full-column minor; the same minor polynomial is nonzero at some real
point, where it certifies injectivity of the whole matrix.  Again the entries
may have arbitrary degree, so this includes the requested linear-entry case. -/
theorem exists_real_specialization_injective_of_complex
    {σ m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (MvPolynomial σ ℤ))
    (hComplex : ∃ z : σ → ℂ,
      Function.Injective (specializeMatrix (Int.castRingHom ℂ) z A).mulVec) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  obtain ⟨z, hz⟩ := hComplex
  obtain ⟨rows, hrows⟩ := exists_fullColumnMinor_of_mulVec_injective
    (specializeMatrix (Int.castRingHom ℂ) z A) hz
  apply exists_real_specialization_injective_of_complex_minor A rows
  refine ⟨z, ?_⟩
  simpa [specializeMatrix, Matrix.submatrix_map] using hrows

end ComplexRealSpecialization

end RB31E2E
