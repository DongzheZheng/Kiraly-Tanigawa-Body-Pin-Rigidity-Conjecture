import RB31EndToEnd.Linear.DirectionStressBaseChange

/-!
# Descent of a virtual direction response through a field extension

For a placement defined over `L`, a direction row belongs to the span of
the old direction rows over `L` exactly when its coordinatewise scalar
extension belongs to their span over `K`.  The reverse implication used below
is proved by comparing the ranks before and after
inserting the virtual row, using the already established invariance of
direction rank under field extension.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {L K V : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype V] [DecidableEq V]

/-- Scalar extension transports membership in a literal direction-row
space. -/
theorem directionRow_mem_mapPlacement_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V)
    (hrow : directionRow a e ∈ directionRowSpace F a) :
    directionRow (mapPlacement (K := K) a) e ∈
      directionRowSpace F (mapPlacement (K := K) a) := by
  -- Avoid choosing row coefficients: compare ranks after adjoining `e`.
  have hInsertL : directionRowSpace (insert e F) a =
      directionRowSpace F a :=
    directionRowSpace_insert_eq_of_mem F a e hrow
  have hRankL : directionEquilibriumRank (insert e F) a =
      directionEquilibriumRank F a := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace, hInsertL]
  have hRankK :
      directionEquilibriumRank (insert e F) (mapPlacement (K := K) a) =
        directionEquilibriumRank F (mapPlacement (K := K) a) := by
    rw [directionEquilibriumRank_mapPlacement,
      directionEquilibriumRank_mapPlacement, hRankL]
  have hLe := directionRowSpace_le_insert F
    (mapPlacement (K := K) a) e
  have hEq : directionRowSpace (insert e F) (mapPlacement (K := K) a) =
      directionRowSpace F (mapPlacement (K := K) a) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRankK.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨e, Finset.mem_insert_self e F⟩, rfl⟩

/-- If a row defined over the smaller field is a virtual response after
scalar extension, it was already a virtual response over the smaller
field. -/
theorem directionRow_mem_of_mapPlacement_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V)
    (hrow : directionRow (mapPlacement (K := K) a) e ∈
      directionRowSpace F (mapPlacement (K := K) a)) :
    directionRow a e ∈ directionRowSpace F a := by
  have hInsertK :
      directionRowSpace (insert e F) (mapPlacement (K := K) a) =
        directionRowSpace F (mapPlacement (K := K) a) :=
    directionRowSpace_insert_eq_of_mem F
      (mapPlacement (K := K) a) e hrow
  have hRankK :
      directionEquilibriumRank (insert e F) (mapPlacement (K := K) a) =
        directionEquilibriumRank F (mapPlacement (K := K) a) := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace, hInsertK]
  have hRankL : directionEquilibriumRank (insert e F) a =
      directionEquilibriumRank F a := by
    simpa only [directionEquilibriumRank_mapPlacement] using hRankK
  have hLe := directionRowSpace_le_insert F a e
  have hEq : directionRowSpace (insert e F) a = directionRowSpace F a := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hLe
    simpa only [directionEquilibriumRank_eq_finrank_rowSpace] using hRankL.symm
  rw [← hEq]
  apply Submodule.subset_span
  exact ⟨⟨e, Finset.mem_insert_self e F⟩, rfl⟩

/-- Hence response-row membership is equivalent before and after scalar
extension. -/
theorem directionRow_mem_mapPlacement_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → L) (e : SimpleEdge V) :
    directionRow (mapPlacement (K := K) a) e ∈
        directionRowSpace F (mapPlacement (K := K) a) ↔
      directionRow a e ∈ directionRowSpace F a := by
  constructor
  · exact directionRow_mem_of_mapPlacement_mem F a e
  · exact directionRow_mem_mapPlacement_of_mem F a e

end

end DirectionStress

end RB31E2E
