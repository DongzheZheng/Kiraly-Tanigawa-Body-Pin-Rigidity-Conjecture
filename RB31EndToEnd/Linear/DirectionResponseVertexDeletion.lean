import RB31EndToEnd.Linear.DirectionResponseBaseChange
import RB31EndToEnd.Linear.DirectionStressVertexDeletion
import RB31EndToEnd.NullCellule.ProvenanceFlagDeletionLedger

/-!
# Virtual responses under literal vertex deletion

This file combines the cross-type vertex-deletion equivalence with the
virtual-row augmentation calculus.  A response edge avoiding the deleted
vertex may be inserted either before deletion or after restricting to the
remaining-vertex subtype; the two presentations have the same stress
dimension.  Consequently a virtual response row in the parent deleted
graph becomes a virtual response row in the literal child graph, and then
descends further to the child's intrinsic coordinate field.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

open ProvenanceFlag Sparse22Transport

variable {L K V : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Restricting after inserting an edge which avoids `v` is literally
insertion of the restricted edge. -/
theorem restrictedLiveEdges_insert
    (F : SimpleEdgeSet V) (v : V) (f : SimpleEdge V)
    (hvf : v ∉ f.vertices) :
    restrictedLiveEdges (insert f F) v =
      insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v) := by
  ext e
  rw [mem_restrictedLiveEdges_iff]
  constructor
  · intro he
    obtain ⟨heParent, heAvoid⟩ := mem_deleteVertexEdges.mp he
    rcases Finset.mem_insert.mp heParent with heEq | heF
    · rw [Finset.mem_insert]
      left
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [map_restrictSimpleEdge, heEq]
    · rw [Finset.mem_insert]
      right
      rw [mem_restrictedLiveEdges_iff]
      exact mem_deleteVertexEdges.mpr ⟨heF, heAvoid⟩
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with heEq | heOld
    · subst e
      rw [map_restrictSimpleEdge]
      exact mem_deleteVertexEdges.mpr
        ⟨Finset.mem_insert_self _ _, hvf⟩
    · rw [mem_restrictedLiveEdges_iff] at heOld
      obtain ⟨heF, heAvoid⟩ := mem_deleteVertexEdges.mp heOld
      exact mem_deleteVertexEdges.mpr
        ⟨Finset.mem_insert_of_mem heF, heAvoid⟩

omit [Fintype V] in
/-- Stress after inserting an avoiding edge agrees in the parent-deleted
and literal-child presentations. -/
theorem directionStressDim_insert_restricted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices) :
    directionStressDim
        (insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v))
        (restrictPlacement a v) =
      directionStressDim (insert f (deleteVertexEdges F v)) a := by
  rw [← restrictedLiveEdges_insert F v f hvf]
  rw [directionStressDim_restrictedLiveEdges]
  congr 2
  ext e
  simp only [mem_deleteVertexEdges, Finset.mem_insert]
  constructor
  · rintro ⟨he, heAvoid⟩
    exact he.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h, heAvoid⟩)
  · rintro (rfl | ⟨heF, heAvoid⟩)
    · exact ⟨Or.inl rfl, hvf⟩
    · exact ⟨Or.inr heF, heAvoid⟩

/-- Converse to virtual augmentation: for an absent edge, gaining exactly
one stress after insertion forces its row to have been in the old row
space. -/
theorem directionRow_mem_of_stress_insert_eq_add_one
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (f : SimpleEdge V)
    (hf : f ∉ F)
    (hStress : directionStressDim (insert f F) a =
      directionStressDim F a + 1) :
    directionRow a f ∈ directionRowSpace F a := by
  have hParent := directionStressDim_add_directionEquilibriumRank
    (insert f F) a
  have hOld := directionStressDim_add_directionEquilibriumRank F a
  have hRank : directionEquilibriumRank (insert f F) a =
      directionEquilibriumRank F a := by
    rw [Finset.card_insert_of_notMem hf, hStress] at hParent
    omega
  have hLe := directionRowSpace_le_insert F a f
  have hEq : directionRowSpace (insert f F) a = directionRowSpace F a := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRank.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨f, Finset.mem_insert_self _ _⟩, rfl⟩

/-- An ambient virtual response in the parent deleted graph restricts to a
virtual response in the literal child graph. -/
theorem directionRow_restrict_mem_of_deleted_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges F v)
    (hrow : directionRow a f ∈
      directionRowSpace (deleteVertexEdges F v) a) :
    directionRow (restrictPlacement a v) (restrictSimpleEdge v f hvf) ∈
      directionRowSpace (restrictedLiveEdges F v)
        (restrictPlacement a v) := by
  have hParentStress := directionStressDim_insert_eq_add_one_of_row_mem
    (deleteVertexEdges F v) a f hf hrow
  have hChildOld := directionStressDim_restrictedLiveEdges F a v
  have hChildInserted :=
    directionStressDim_insert_restricted F a v f hvf
  have hChildStress :
      directionStressDim
          (insert (restrictSimpleEdge v f hvf) (restrictedLiveEdges F v))
          (restrictPlacement a v) =
        directionStressDim (restrictedLiveEdges F v)
          (restrictPlacement a v) + 1 := by
    rw [hChildInserted, hParentStress, hChildOld]
  have hfChild : restrictSimpleEdge v f hvf ∉ restrictedLiveEdges F v := by
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hf hmem
  exact directionRow_mem_of_stress_insert_eq_add_one
    (restrictedLiveEdges F v) (restrictPlacement a v)
    (restrictSimpleEdge v f hvf) hfChild hChildStress

/-- Final intrinsic form: if the parent ambient deleted graph carries a
virtual response edge, then the same restricted edge is in the child row
space over the field generated by the retained coordinates. -/
theorem directionRow_intrinsicRestricted_mem_of_deleted_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges F v)
    (hrow : directionRow a f ∈
      directionRowSpace (deleteVertexEdges F v) a) :
    directionRow
        (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v)
        (restrictSimpleEdge v f hvf) ∈
      directionRowSpace (restrictedLiveEdges F v)
        (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v) := by
  apply directionRow_mem_of_mapPlacement_mem
    (K := K) (restrictedLiveEdges F v)
    (ProvenanceFlag.intrinsicRestrictedPlacement (k := L) a v)
    (restrictSimpleEdge v f hvf)
  rw [ProvenanceFlag.map_intrinsicRestrictedPlacement]
  exact directionRow_restrict_mem_of_deleted_mem F a v f hvf hf hrow

end

end DirectionStress

end RB31E2E
