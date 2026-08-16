import RB31EndToEnd.Linear.PrivatePivotStress

/-!
# Stress payment for registering a complete collinear triangle

If all three edges of a triangle are live and its three placed vertices are
distinct and collinear, deleting any one triangle row lowers stress nullity
by exactly one.  The remaining two rows span the deleted row, so rank stays
fixed while the labelled edge count drops by one.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {K V : Type*}
  [Field K] [Fintype V] [DecidableEq V]

/-- Erasing the `pq` row of a complete collinear triangle lowers the stress
dimension by one. -/
theorem directionStressDim_eq_erase_triangle_add_one
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (p q r : V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqMem : simpleEdge p q hpq ∈ F)
    (hprMem : simpleEdge p r hpr ∈ F)
    (hqrMem : simpleEdge q r hqr ∈ F)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos p) (pos q) (pos r)) :
    directionStressDim F pos =
      directionStressDim (F.erase (simpleEdge p q hpq)) pos + 1 := by
  let F0 := F.erase (simpleEdge p q hpq)
  have hpr_ne_pq : simpleEdge p r hpr ≠ simpleEdge p q hpq := by
    intro h
    rw [simpleEdge_eq_simpleEdge_iff] at h
    rcases h with h | h
    · exact hqr h.2.symm
    · exact hpq h.1
  have hqr_ne_pq : simpleEdge q r hqr ≠ simpleEdge p q hpq := by
    intro h
    rw [simpleEdge_eq_simpleEdge_iff] at h
    rcases h with h | h
    · exact hpq h.1.symm
    · exact hpr h.2.symm
  have hprF0 : simpleEdge r p hpr.symm ∈ F0 := by
    rw [simpleEdge_comm r p hpr.symm]
    exact Finset.mem_erase.mpr ⟨hpr_ne_pq, hprMem⟩
  have hqrF0 : simpleEdge r q hqr.symm ∈ F0 := by
    rw [simpleEdge_comm r q hqr.symm]
    exact Finset.mem_erase.mpr ⟨hqr_ne_pq, hqrMem⟩
  have hcolRPQ :
      PinCollinearity.Collinear (pos r) (pos p) (pos q) :=
    collinear_cycle (pos q) (pos r) (pos p)
      (collinear_cycle (pos p) (pos q) (pos r) hcol)
  have hrow : directionRow pos (simpleEdge p q hpq) ∈
      directionRowSpace F0 pos := by
    exact triangleThirdRow_mem_of_collinear F0 pos r p q
      hpr.symm hqr.symm hpq hprF0 hqrF0 hpos hcolRPQ
  have hAug := directionStressDim_insert_eq_add_one_of_row_mem
    F0 pos (simpleEdge p q hpq) (by simp [F0]) hrow
  have hRecover : insert (simpleEdge p q hpq) F0 = F := by
    exact Finset.insert_erase hpqMem
  rw [hRecover] at hAug
  exact hAug

end

end DirectionStress

end RB31E2E
