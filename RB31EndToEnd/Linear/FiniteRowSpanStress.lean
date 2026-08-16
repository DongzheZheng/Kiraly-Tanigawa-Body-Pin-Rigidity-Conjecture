import RB31EndToEnd.Linear.FiniteRowSystem

/-! # Row-span/stress rank--nullity -/

namespace RB31E2E

namespace FiniteRowSystem

noncomputable section

variable {k I J : Type*} [Field k] [Fintype I] [Fintype J]

/-- The dimension of the literal row span plus the dimension of the row
relation kernel is exactly the number of labelled rows. -/
theorem finrank_span_add_stressDim_eq_card (row : J → I → k) :
    Module.finrank k (Submodule.span k (Set.range row)) +
      stressDim row = Fintype.card J := by
  have hs := (synthesis row).finrank_range_add_finrank_ker
  have hrange :
      Module.finrank k (LinearMap.range (synthesis row)) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    change (matrix row).transpose.rank = _
    rw [Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row]
    rfl
  have hdomain : Module.finrank k (J → k) = Fintype.card J := by
    rw [Module.finrank_fintype_fun_eq_card]
  change Module.finrank k (LinearMap.range (synthesis row)) +
      stressDim row = Module.finrank k (J → k) at hs
  simpa [hrange, hdomain] using hs

end

end FiniteRowSystem

end RB31E2E
