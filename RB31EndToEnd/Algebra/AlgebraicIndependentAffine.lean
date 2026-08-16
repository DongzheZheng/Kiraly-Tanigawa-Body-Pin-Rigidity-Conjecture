import RB31EndToEnd.Algebra.FiniteCoordinateTrdeg

/-!
# Affine linear independence from algebraic independence

An algebraically independent family remains linearly independent after a
single constant `1` is adjoined.  This small coefficient-comparison lemma is
the exact algebraic input used by the full three-coordinate response step;
it is proved from injectivity of multivariate polynomial evaluation, rather
than assumed as an affine-genericity predicate.
-/

namespace RB31E2E

namespace AlgebraicIndependentAffine

noncomputable section

open Set Submodule

variable {L K I : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The constant one is not in the linear span of an algebraically
independent family. -/
theorem one_not_mem_span_range
    (x : I → K) (hx : AlgebraicIndependent L x) :
    (1 : K) ∉ Submodule.span L (Set.range x) := by
  intro hOne
  obtain ⟨c : I → L, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun L).mp hOne
  let P : MvPolynomial I L :=
    MvPolynomial.C 1 -
      ∑ i : I, MvPolynomial.C (c i) * MvPolynomial.X i
  have hEval : MvPolynomial.aeval x P = 0 := by
    dsimp [P]
    simp only [map_sub, map_one, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rw [show (∑ i : I, algebraMap L K (c i) * x i) = 1 by
      simpa [Algebra.smul_def] using hc]
    exact sub_self 1
  have hPzero : P = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp hx)
      (by simpa using hEval)
  have hAtZero := congrArg
    (MvPolynomial.eval (fun _ : I ↦ (0 : L))) hPzero
  simp [P] at hAtZero

omit [DecidableEq I] in
/-- Adjoining the constant coordinate to an algebraically independent
finite family gives an affine-linearly independent `Option` family. -/
theorem option_one_linearIndependent
    (x : I → K) (hx : AlgebraicIndependent L x) :
    LinearIndependent L (fun o : Option I ↦ o.casesOn' (1 : K) x) := by
  exact hx.linearIndependent.option (one_not_mem_span_range x hx)

end

end AlgebraicIndependentAffine

end RB31E2E
