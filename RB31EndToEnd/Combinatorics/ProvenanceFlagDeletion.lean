import RB31EndToEnd.Combinatorics.ProvenanceFlagSelection
import RB31EndToEnd.Combinatorics.Sparse22.Transport
import RB31EndToEnd.Linear.DirectionStress

/-!
# Deleting an outside live vertex from a provenance-flag state

The provenance induction changes its literal live-vertex type after a
deletion.  This file constructs that child state rather than postulating
it.  If `v` belongs to no active flag, every terminal, missing edge, live
edge, and ghost star restricts to the subtype of vertices different from
`v`.  The child's completed graph maps edge-for-edge into the parent's
completed graph, so completion sparsity descends by the already proved
transport theorem.

No stress, response, semismallness, or height statement is stored in the
child state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open Sparse22Transport

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact live-vertex type after deleting `v`. -/
abbrev RemainingVertex (v : V) := {u : V // u ≠ v}

/-- Inclusion of the remaining live vertices into the parent type. -/
def remainingVertexEmbedding (v : V) : RemainingVertex v ↪ V :=
  Function.Embedding.subtype _

/-- Inclusion of a child completion into the parent completion. -/
def remainingCompletionEmbedding (v : V) :
    (RemainingVertex v ⊕ Flag) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr t => Sum.inr t
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at h
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
        | inr y =>
            change Sum.inl (x.1 : V) = Sum.inr y at h
            exact False.elim (Sum.inl_ne_inr h)
    | inr x =>
        cases y with
        | inl y =>
            change Sum.inr x = Sum.inl (y.1 : V) at h
            exact False.elim (Sum.inr_ne_inl h)
        | inr y =>
            change Sum.inr x = Sum.inr y at h
            exact congrArg Sum.inr (Sum.inr.inj h)

omit [Fintype V] in
private theorem source_mem_vertices (e : SimpleEdge V) :
    e.source ∈ e.vertices := by
  rw [SimpleEdge.vertices, ← e.source_target_mk]
  simp [Sym2.toFinset_mk_eq]

omit [Fintype V] in
private theorem target_mem_vertices (e : SimpleEdge V) :
    e.target ∈ e.vertices := by
  rw [SimpleEdge.vertices, ← e.source_target_mk]
  simp [Sym2.toFinset_mk_eq]

/-- Restrict a parent edge which avoids `v` to the remaining subtype. -/
def restrictSimpleEdge (v : V) (e : SimpleEdge V)
    (hv : v ∉ e.vertices) : SimpleEdge (RemainingVertex v) :=
  simpleEdge
    ⟨e.source, fun h => hv (h ▸ source_mem_vertices e)⟩
    ⟨e.target, fun h => hv (h ▸ target_mem_vertices e)⟩
    (by
      intro h
      exact e.source_ne_target (congrArg Subtype.val h))

omit [Fintype V] in
@[simp]
theorem map_restrictSimpleEdge (v : V) (e : SimpleEdge V)
    (hv : v ∉ e.vertices) :
    mapSimpleEdge (remainingVertexEmbedding v) (restrictSimpleEdge v e hv) = e := by
  apply Subtype.ext
  rw [mapSimpleEdge_val]
  simp only [restrictSimpleEdge, simpleEdge, Sym2.map_mk]
  exact e.source_target_mk

/-- A deleted parent edge, reindexed on the remaining vertex type. -/
def restrictDeletedEdge (F : SimpleEdgeSet V) (v : V)
    (e : deleteVertexEdges F v) : SimpleEdge (RemainingVertex v) :=
  restrictSimpleEdge v e.1 (mem_deleteVertexEdges.mp e.2).2

omit [Fintype V] in
theorem restrictDeletedEdge_injective (F : SimpleEdgeSet V) (v : V) :
    Function.Injective (restrictDeletedEdge F v) := by
  intro e f h
  have := congrArg (mapSimpleEdge (remainingVertexEmbedding v)) h
  apply Subtype.ext
  simpa [restrictDeletedEdge] using this

/-- Embedding of the deleted parent edge subtype into child edges. -/
def restrictDeletedEdgeEmbedding (F : SimpleEdgeSet V) (v : V) :
    deleteVertexEdges F v ↪ SimpleEdge (RemainingVertex v) where
  toFun := restrictDeletedEdge F v
  inj' := restrictDeletedEdge_injective F v

/-- The literal child live edge set. -/
def restrictedLiveEdges (F : SimpleEdgeSet V) (v : V) :
    SimpleEdgeSet (RemainingVertex v) :=
  (deleteVertexEdges F v).attach.map (restrictDeletedEdgeEmbedding F v)

omit [Fintype V] in
@[simp]
theorem mem_restrictedLiveEdges_iff
    (F : SimpleEdgeSet V) (v : V) (e : SimpleEdge (RemainingVertex v)) :
    e ∈ restrictedLiveEdges F v ↔
      mapSimpleEdge (remainingVertexEmbedding v) e ∈ deleteVertexEdges F v := by
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictDeletedEdge F v f) ∈ deleteVertexEdges F v
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]
    exact f.2
  · intro he
    let f : deleteVertexEdges F v :=
      ⟨mapSimpleEdge (remainingVertexEmbedding v) e, he⟩
    have hMap : restrictDeletedEdge F v f = e := by
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      unfold restrictDeletedEdge
      rw [map_restrictSimpleEdge]
    exact Finset.mem_map.mpr ⟨f, Finset.mem_attach _ f, hMap⟩

omit [Fintype V] in
theorem map_restrictedLiveEdges (F : SimpleEdgeSet V) (v : V) :
    mapEdgeSet (remainingVertexEmbedding v) (restrictedLiveEdges F v) =
      deleteVertexEdges F v := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    exact (mem_restrictedLiveEdges_iff F v f).1 hf
  · intro he
    let f : deleteVertexEdges F v := ⟨e, he⟩
    let g := restrictDeletedEdge F v f
    have hg : g ∈ restrictedLiveEdges F v := by
      exact Finset.mem_map.mpr ⟨f, Finset.mem_attach _ f, rfl⟩
    refine Finset.mem_map.mpr ⟨g, hg, ?_⟩
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictDeletedEdge F v f) = e
    unfold restrictDeletedEdge
    rw [map_restrictSimpleEdge]

/-- Restrict a finite vertex set known not to contain `v`. -/
def restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    Finset (RemainingVertex v) :=
  X.attach.map
    { toFun := fun x => ⟨x.1, fun h => hv (h ▸ x.2)⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : RemainingVertex v => z.1) h }

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mem_restrictVertexSet_iff (v : V) (X : Finset V) (hv : v ∉ X)
    (u : RemainingVertex v) :
    u ∈ restrictVertexSet v X hv ↔ u.1 ∈ X := by
  constructor
  · intro hu
    unfold restrictVertexSet at hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_map.mp hu
    have hval : x.1 = u.1 := congrArg Subtype.val hxu
    exact hval ▸ x.2
  · intro hu
    let x : X := ⟨u.1, hu⟩
    unfold restrictVertexSet
    exact Finset.mem_map.mpr ⟨x, Finset.mem_attach _ x, Subtype.ext rfl⟩

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem card_restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    (restrictVertexSet v X hv).card = X.card := by
  simp [restrictVertexSet]

omit [Fintype V] [DecidableEq V] in
theorem map_restrictVertexSet (v : V) (X : Finset V) (hv : v ∉ X) :
    (restrictVertexSet v X hv).map (remainingVertexEmbedding v) = X := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_map.mp hu
    exact hxu.symm ▸
      (mem_restrictVertexSet_iff v X hv x).1 hx
  · intro hu
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    let x : RemainingVertex v := ⟨u, huv⟩
    exact Finset.mem_map.mpr
      ⟨x, (mem_restrictVertexSet_iff v X hv x).2 hu, rfl⟩

omit [Fintype V] in
/-- Endpoint membership is preserved by restriction to the avoiding
subtype. -/
@[simp]
theorem mem_restrictSimpleEdge_vertices_iff
    (v : V) (e : SimpleEdge V) (hv : v ∉ e.vertices)
    (u : RemainingVertex v) :
    u ∈ (restrictSimpleEdge v e hv).vertices ↔ u.1 ∈ e.vertices := by
  rw [restrictSimpleEdge, vertices_simpleEdge, SimpleEdge.vertices,
    ← e.source_target_mk, Sym2.toFinset_mk_eq]
  constructor
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hu))
    · have hu' : u =
          (⟨e.target, fun h => hv (h ▸ target_mem_vertices e)⟩ :
            RemainingVertex v) := by simpa using hu
      exact Finset.mem_insert.mpr
        (Or.inr (by simpa using congrArg Subtype.val hu'))
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact Finset.mem_insert.mpr
        (Or.inl (Subtype.ext (by simpa using hu)))
    · exact Finset.mem_insert.mpr
        (Or.inr (by
          rw [Finset.mem_singleton]
          apply Subtype.ext
          simpa using hu))

/-- Every endpoint of an edge mapped from the avoiding subtype still
avoids the deleted vertex. -/
theorem deleted_not_mem_mapped_vertices
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    v ∉ (mapSimpleEdge (remainingVertexEmbedding v) e).vertices := by
  intro hvEdge
  have hsub := mapSimpleEdge_vertices_subset
    (remainingVertexEmbedding v) e (Finset.univ : Finset (RemainingVertex v))
    (by simp)
  have hvRange := hsub hvEdge
  obtain ⟨u, _hu, huv⟩ := Finset.mem_map.mp hvRange
  exact u.2 huv

/-- An outside vertex occurs in no active terminal triple. -/
theorem not_mem_terminals_of_flagMultiplicity_eq_zero
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (t : Flag) : v ∉ S.terminals t := by
  intro hvt
  have ht : t ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v t).2 hvt
  have : 0 < S.flagMultiplicity v := by
    rw [State.flagMultiplicity]
    exact Finset.card_pos.mpr ⟨t, ht⟩
  omega

/-- The missing edge of a flag avoids an outside vertex. -/
theorem outside_not_mem_missing_vertices
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (t : Flag) : v ∉ (S.missing t).vertices := by
  intro hve
  exact not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t
    (S.missing_supported t hve)

/-- Delete an outside vertex and reindex all surviving provenance data. -/
def State.deleteOutside (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) : State (RemainingVertex v) Flag where
  edges := restrictedLiveEdges S.edges v
  terminals t := restrictVertexSet v (S.terminals t)
    (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t)
  missing t := restrictSimpleEdge v (S.missing t)
    (outside_not_mem_missing_vertices S v hv t)
  terminals_card t := by
    rw [card_restrictVertexSet, S.terminals_card]
  missing_supported t := by
    intro u hu
    rw [mem_restrictVertexSet_iff]
    apply S.missing_supported t
    exact (mem_restrictSimpleEdge_vertices_iff _ _ _ u).1 hu
  missing_not_live t := by
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge]
    simp [S.missing_not_live t]
  other_terminal_edges_live t e heT heMissing := by
    rw [mem_restrictedLiveEdges_iff]
    refine mem_deleteVertexEdges.mpr ⟨?_, deleted_not_mem_mapped_vertices v e⟩
    apply S.other_terminal_edges_live t
    · have hsub := mapSimpleEdge_vertices_subset
          (remainingVertexEmbedding v) e
          (restrictVertexSet v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t)) heT
      simpa [map_restrictVertexSet] using hsub
    · intro hEq
      apply heMissing
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [hEq, map_restrictSimpleEdge]

@[simp]
theorem deleteOutside_edges (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) :
    (S.deleteOutside v hv).edges = restrictedLiveEdges S.edges v := rfl

@[simp]
theorem deleteOutside_terminals (S : State V Flag) (v : V)
    (hv : S.flagMultiplicity v = 0) (t : Flag) :
    (S.deleteOutside v hv).terminals t =
      restrictVertexSet v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_remaining
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag) e) =
      liftLiveEdge (Flag := Flag)
        (mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [mapSimpleEdge_val, liftLiveEdge_val, Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [remainingCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_remaining
    (v : V) (t : Flag) (u : RemainingVertex v) :
    mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (ghostEdge t u) = ghostEdge t u.1 := by
  apply Subtype.ext
  change s(Sum.inr t, Sum.inl u.1) = s(Sum.inr t, Sum.inl u.1)
  rfl

/-- The completed outside child embeds edge-for-edge in the completed
parent. -/
theorem map_deleteOutside_completionEdges_subset
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    mapEdgeSet (remainingCompletionEmbedding (Flag := Flag) v)
        (S.deleteOutside v hv).completionEdges ⊆ S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
          (liftLiveEdge (Flag := Flag) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_remaining]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hg)).1
    · obtain ⟨t, _ht, hft⟩ := Finset.mem_image.mp hfMissing
      subst f
      change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
          (liftLiveEdge (Flag := Flag)
            ((S.deleteOutside v hv).missing t)) ∈ S.completionEdges
      have hmissing : (S.deleteOutside v hv).missing t =
          restrictSimpleEdge v (S.missing t)
            (outside_not_mem_missing_vertices S v hv t) := rfl
      rw [hmissing, map_liftLiveEdge_remaining, map_restrictSimpleEdge]
      exact S.lifted_missing_mem_completionEdges t
  · obtain ⟨t, _ht, hft⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hft
    subst f
    change mapSimpleEdge (remainingCompletionEmbedding (Flag := Flag) v)
        (ghostEdge t u) ∈ S.completionEdges
    rw [map_ghostEdge_remaining]
    exact S.ghostEdge_mem_completionEdges t
      ((mem_restrictVertexSet_iff v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) u).1 hu)

/-- Completion sparsity descends under deletion of an outside vertex. -/
theorem State.deleteOutside_completionSparse
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (hSparse : S.CompletionSparse) :
    (S.deleteOutside v hv).CompletionSparse := by
  exact sparse22_of_mapEdgeSet_subset
    (remainingCompletionEmbedding (Flag := Flag) v)
    hSparse (map_deleteOutside_completionEdges_subset S v hv)

end ProvenanceFlag

end

end RB31E2E
