import RB31EndToEnd.Combinatorics.ProvenanceFlagPrivateDeletion
import RB31EndToEnd.Linear.PrivateLocalClassification

/-!
# Reindexing direction stresses after a literal vertex deletion

`restrictedLiveEdges F v` is a graph on the subtype of vertices different
from `v`, whereas `deleteVertexEdges F v` retains the parent vertex type.
This file proves that these are not merely equinumerous presentations: the
actual direction-stress kernels are linearly equivalent after restricting
the placement.  This is the cross-type bridge needed to apply induction to
the child `State` and the deletion exact sequence to the parent graph.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

open ProvenanceFlag Sparse22Transport

/-- Restriction of a placement to the literal remaining-vertex subtype. -/
def restrictPlacement (a : V → Fin 3 → k) (v : V) :
    RemainingVertex v → Fin 3 → k :=
  fun u ↦ a u.1

/-- The child-edge subtype and the deleted parent-edge subtype are
canonically equivalent. -/
def restrictedEdgeEquiv (F : SimpleEdgeSet V) (v : V) :
    ↑(restrictedLiveEdges F v) ≃ ↑(deleteVertexEdges F v) where
  toFun e :=
    ⟨mapSimpleEdge (remainingVertexEmbedding v) e.1,
      (mem_restrictedLiveEdges_iff F v e.1).1 e.2⟩
  invFun e :=
    ⟨restrictDeletedEdge F v e,
      Finset.mem_map.mpr ⟨e, Finset.mem_attach _ e, rfl⟩⟩
  left_inv e := by
    apply Subtype.ext
    apply mapSimpleEdge_injective (remainingVertexEmbedding v)
    change mapSimpleEdge (remainingVertexEmbedding v)
      (restrictDeletedEdge F v
        ⟨mapSimpleEdge (remainingVertexEmbedding v) e.1, _⟩) =
      mapSimpleEdge (remainingVertexEmbedding v) e.1
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
  right_inv e := by
    apply Subtype.ext
    change mapSimpleEdge (remainingVertexEmbedding v)
      (restrictDeletedEdge F v e) = e.1
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]

/-- Reindex edge-weight functions along the canonical deleted-edge
equivalence. -/
def restrictedEdgeWeightEquiv (F : SimpleEdgeSet V) (v : V) :
    (restrictedLiveEdges F v → k) ≃ₗ[k]
      (deleteVertexEdges F v → k) where
  toFun weight e := weight ((restrictedEdgeEquiv F v).symm e)
  invFun weight e := weight (restrictedEdgeEquiv F v e)
  left_inv weight := by
    funext e
    simp
  right_inv weight := by
    funext e
    simp
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

omit [Fintype V] in
/-- Restricting a parent edge which avoids `v` preserves its direction row
at every remaining vertex. -/
theorem directionRow_restrictSimpleEdge
    (a : V → Fin 3 → k) (v : V) (e : SimpleEdge V)
    (hve : v ∉ e.vertices) (u : RemainingVertex v) :
    directionRow (restrictPlacement a v) (restrictSimpleEdge v e hve) u =
      directionRow a e u.1 := by
  let source : RemainingVertex v :=
    ⟨e.source, fun h ↦ hve (h ▸ by
      rw [SimpleEdge.vertices, ← e.source_target_mk]
      simp [Sym2.toFinset_mk_eq])⟩
  let target : RemainingVertex v :=
    ⟨e.target, fun h ↦ hve (h ▸ by
      rw [SimpleEdge.vertices, ← e.source_target_mk]
      simp [Sym2.toFinset_mk_eq])⟩
  have hParent : e = simpleEdge e.source e.target e.source_ne_target := by
    apply Subtype.ext
    exact e.source_target_mk.symm
  have hChild : restrictSimpleEdge v e hve =
      simpleEdge source target (by
        intro h
        exact e.source_ne_target (congrArg Subtype.val h)) := by
    rfl
  rw [hChild]
  conv_rhs => rw [hParent]
  by_cases huSource : u = source
  · subst u
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left]
    rfl
  · by_cases huTarget : u = target
    · subst u
      rw [directionRow_simpleEdge_at_right,
        directionRow_simpleEdge_at_right]
      rfl
    · rw [directionRow_simpleEdge_at_other]
      · rw [directionRow_simpleEdge_at_other]
        · exact fun h ↦ huSource (Subtype.ext h)
        · exact fun h ↦ huTarget (Subtype.ext h)
      · exact huSource
      · exact huTarget

omit [Fintype V] in
/-- Mapping a child edge to the deleted parent presentation preserves its
direction row on remaining vertices. -/
theorem directionRow_restrictedEdgeEquiv
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (e : restrictedLiveEdges F v) (u : RemainingVertex v) :
    directionRow (restrictPlacement a v) e.1 u =
      directionRow a (restrictedEdgeEquiv F v e).1 u.1 := by
  let E : deleteVertexEdges F v := restrictedEdgeEquiv F v e
  have hAvoid : v ∉ E.1.vertices := (mem_deleteVertexEdges.mp E.2).2
  have hRestrict : restrictDeletedEdge F v E = e.1 := by
    apply mapSimpleEdge_injective (remainingVertexEmbedding v)
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
    rfl
  rw [← hRestrict]
  exact directionRow_restrictSimpleEdge a v E.1 hAvoid u

omit [Fintype V] in
/-- Equilibrium synthesis commutes with the cross-type deletion reindexing. -/
theorem directionEquilibrium_restricted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (weight : restrictedLiveEdges F v → k) (u : RemainingVertex v) :
    directionEquilibrium (restrictedLiveEdges F v)
        (restrictPlacement a v) weight u =
      directionEquilibrium (deleteVertexEdges F v) a
        (restrictedEdgeWeightEquiv F v weight) u.1 := by
  funext j
  change (∑ e : restrictedLiveEdges F v,
      weight e * directionRow (restrictPlacement a v) e.1 u j) =
    ∑ e : deleteVertexEdges F v,
      (restrictedEdgeWeightEquiv F v weight) e *
        directionRow a e.1 u.1 j
  exact Fintype.sum_equiv (restrictedEdgeEquiv F v)
    (fun e : restrictedLiveEdges F v ↦
      weight e * directionRow (restrictPlacement a v) e.1 u j)
    (fun e : deleteVertexEdges F v ↦
      (restrictedEdgeWeightEquiv F v weight) e *
        directionRow a e.1 u.1 j)
    (fun e ↦ by
      change weight e * directionRow (restrictPlacement a v) e.1 u j =
        (restrictedEdgeWeightEquiv F v weight) (restrictedEdgeEquiv F v e) *
          directionRow a (restrictedEdgeEquiv F v e).1 u.1 j
      rw [directionRow_restrictedEdgeEquiv F a v e u]
      simp [restrictedEdgeWeightEquiv])

/-- The literal stress spaces in the subtype child and deleted parent
presentations are linearly equivalent. -/
def restrictedStressEquiv
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    DirectionStressSpace (restrictedLiveEdges F v) (restrictPlacement a v) ≃ₗ[k]
      DirectionStressSpace (deleteVertexEdges F v) a where
  toFun weight := by
    refine ⟨restrictedEdgeWeightEquiv F v weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    by_cases huv : u = v
    · subst u
      exact old_packet_equilibrium_at_deleted F a v
        (restrictedEdgeWeightEquiv F v weight.1)
    · let ur : RemainingVertex v := ⟨u, huv⟩
      have hChild := LinearMap.mem_ker.mp weight.2
      have hChildAt := congrFun hChild ur
      rw [directionEquilibrium_restricted F a v weight.1 ur] at hChildAt
      exact hChildAt
  invFun weight := by
    refine ⟨(restrictedEdgeWeightEquiv F v).symm weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    rw [directionEquilibrium_restricted]
    rw [(restrictedEdgeWeightEquiv F v).apply_symm_apply]
    have hParent := LinearMap.mem_ker.mp weight.2
    have hAt := congrFun hParent u.1
    exact hAt
  left_inv weight := by
    apply Subtype.ext
    exact (restrictedEdgeWeightEquiv F v).symm_apply_apply weight.1
  right_inv weight := by
    apply Subtype.ext
    exact (restrictedEdgeWeightEquiv F v).apply_symm_apply weight.1
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

omit [Fintype V] in
/-- Stress nullity is exactly invariant under the literal child reindexing. -/
theorem directionStressDim_restrictedLiveEdges
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    directionStressDim (restrictedLiveEdges F v) (restrictPlacement a v) =
      directionStressDim (deleteVertexEdges F v) a := by
  exact (restrictedStressEquiv F a v).finrank_eq

end

end DirectionStress

end RB31E2E
