import RB31EndToEnd.Combinatorics.ProvenanceFlagDeletion
import RB31EndToEnd.Combinatorics.ProvenanceFlagInsertion

/-!
# Deleting a private terminal and its unique provenance flag

If `v` belongs to exactly one active flag `t`, the private induction step
removes both the live vertex `v` and the ghost labelled by `t`.  This file
constructs the resulting state on the literal subtype vertex and flag types.
It also transports a certified virtual response-edge insertion to that
child.  All completion and sparsity assertions are proved about the actual
edge sets; no transition conclusion is stored in `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open Sparse22Transport

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact active-flag type after consuming `t`. -/
abbrev RemainingFlag (t : Flag) := {u : Flag // u ≠ t}

/-- Inclusion of the remaining flags into the parent flag type. -/
def remainingFlagEmbedding (t : Flag) : RemainingFlag t ↪ Flag :=
  Function.Embedding.subtype _

/-- Inclusion of the private child completion into the parent completion. -/
def remainingPrivateCompletionEmbedding (v : V) (t : Flag) :
    (RemainingVertex v ⊕ RemainingFlag t) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr r => Sum.inr r.1
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at h
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
        | inr y => exact False.elim (Sum.inl_ne_inr h)
    | inr x =>
        cases y with
        | inl y => exact False.elim (Sum.inr_ne_inl h)
        | inr y =>
            change Sum.inr (x.1 : Flag) = Sum.inr (y.1 : Flag) at h
            exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

/-- A multiplicity-one vertex has no occurrence in any flag other than its
named unique flag. -/
theorem not_mem_other_terminals_of_flagMultiplicity_eq_one
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (u : Flag) (hut : u ≠ t) : v ∉ S.terminals u := by
  have ht : t ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v t).2 hvt
  have hCard : (S.activeFlagsAt v).card = 1 := hOne
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hCard
  have hrt : r = t := by
    rw [hr] at ht
    have htr : t = r := by simpa using ht
    exact htr.symm
  intro hvu
  have hu : u ∈ S.activeFlagsAt v := (S.mem_activeFlagsAt v u).2 hvu
  rw [hr, hrt] at hu
  exact hut (by simpa using hu)

/-- Every retained missing edge avoids the consumed private terminal. -/
theorem private_not_mem_retained_missing_vertices
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (u : RemainingFlag t) : v ∉ (S.missing u.1).vertices := by
  intro hve
  exact not_mem_other_terminals_of_flagMultiplicity_eq_one
    S v t hOne hvt u.1 u.2 (S.missing_supported u.1 hve)

/-- Delete the private live vertex and consume its unique flag. -/
def State.deletePrivate (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    State (RemainingVertex v) (RemainingFlag t) where
  edges := restrictedLiveEdges S.edges v
  terminals u := restrictVertexSet v (S.terminals u.1)
    (not_mem_other_terminals_of_flagMultiplicity_eq_one
      S v t hOne hvt u.1 u.2)
  missing u := restrictSimpleEdge v (S.missing u.1)
    (private_not_mem_retained_missing_vertices S v t hOne hvt u)
  terminals_card u := by
    rw [card_restrictVertexSet, S.terminals_card]
  missing_supported u := by
    intro x hx
    rw [mem_restrictVertexSet_iff]
    apply S.missing_supported u.1
    exact (mem_restrictSimpleEdge_vertices_iff _ _ _ x).1 hx
  missing_not_live u := by
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge]
    simp [S.missing_not_live u.1]
  other_terminal_edges_live u e heT heMissing := by
    rw [mem_restrictedLiveEdges_iff]
    refine mem_deleteVertexEdges.mpr ⟨?_, deleted_not_mem_mapped_vertices v e⟩
    apply S.other_terminal_edges_live u.1
    · have hsub := mapSimpleEdge_vertices_subset
          (remainingVertexEmbedding v) e
          (restrictVertexSet v (S.terminals u.1)
            (not_mem_other_terminals_of_flagMultiplicity_eq_one
              S v t hOne hvt u.1 u.2)) heT
      simpa [map_restrictVertexSet] using hsub
    · intro hEq
      apply heMissing
      apply mapSimpleEdge_injective (remainingVertexEmbedding v)
      rw [hEq, map_restrictSimpleEdge]

@[simp]
theorem deletePrivate_edges
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (S.deletePrivate v t hOne hvt).edges = restrictedLiveEdges S.edges v := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_private
    (v : V) (t : Flag) (e : SimpleEdge (RemainingVertex v)) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t) e) =
      liftLiveEdge (Flag := Flag)
        (mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [mapSimpleEdge_val, liftLiveEdge_val, Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [remainingPrivateCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_private
    (v : V) (t : Flag) (u : RemainingFlag t) (x : RemainingVertex v) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (ghostEdge u x) = ghostEdge u.1 x.1 := by
  apply Subtype.ext
  change s(Sum.inr u.1, Sum.inl x.1) = s(Sum.inr u.1, Sum.inl x.1)
  rfl

/-- The completion of the private-deletion child embeds edge-for-edge in
the parent completion. -/
theorem State.map_deletePrivate_completionEdges_subset
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    mapEdgeSet (remainingPrivateCompletionEmbedding v t)
        (S.deletePrivate v t hOne hvt).completionEdges ⊆
      S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_private]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hg)).1
    · obtain ⟨u, _hu, hfu⟩ := Finset.mem_image.mp hfMissing
      subst f
      change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
          (liftLiveEdge (Flag := RemainingFlag t)
            ((S.deletePrivate v t hOne hvt).missing u)) ∈ S.completionEdges
      have hmissing : (S.deletePrivate v t hOne hvt).missing u =
          restrictSimpleEdge v (S.missing u.1)
            (private_not_mem_retained_missing_vertices
              S v t hOne hvt u) := rfl
      rw [hmissing, map_liftLiveEdge_private, map_restrictSimpleEdge]
      exact S.lifted_missing_mem_completionEdges u.1
  · obtain ⟨u, _hu, hfStar⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hfStar
    subst f
    change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
      (ghostEdge u x) ∈ S.completionEdges
    rw [map_ghostEdge_private]
    exact S.ghostEdge_mem_completionEdges u.1
      ((mem_restrictVertexSet_iff v (S.terminals u.1)
        (not_mem_other_terminals_of_flagMultiplicity_eq_one
          S v t hOne hvt u.1 u.2) x).1 hx)

/-- Completion sparsity descends after consuming a private terminal and its
unique flag. -/
theorem State.deletePrivate_completionSparse
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hSparse : S.CompletionSparse) :
    (S.deletePrivate v t hOne hvt).CompletionSparse := by
  exact sparse22_of_mapEdgeSet_subset
    (remainingPrivateCompletionEmbedding v t)
    hSparse (S.map_deletePrivate_completionEdges_subset v t hOne hvt)

/-! ## Transporting a certified response-edge insertion -/

/-- A mapped private-child completion edge avoids both deleted parent
vertices: the live terminal `v` and the consumed ghost `t`. -/
theorem deletedPrivate_not_mem_mappedCompletionEdge
    (v : V) (t : Flag) (e : SimpleEdge (RemainingVertex v ⊕ RemainingFlag t)) :
    Sum.inl v ∉ (mapSimpleEdge
        (remainingPrivateCompletionEmbedding v t) e).vertices ∧
      Sum.inr t ∉ (mapSimpleEdge
        (remainingPrivateCompletionEmbedding v t) e).vertices := by
  constructor
  · intro hvEdge
    have hsub := mapSimpleEdge_vertices_subset
      (remainingPrivateCompletionEmbedding v t) e
      (Finset.univ : Finset (RemainingVertex v ⊕ RemainingFlag t)) (by simp)
    obtain ⟨x, _hx, hxv⟩ := Finset.mem_map.mp (hsub hvEdge)
    cases x with
    | inl u => exact u.2 (Sum.inl.inj hxv)
    | inr r => exact Sum.inr_ne_inl hxv
  · intro htEdge
    have hsub := mapSimpleEdge_vertices_subset
      (remainingPrivateCompletionEmbedding v t) e
      (Finset.univ : Finset (RemainingVertex v ⊕ RemainingFlag t)) (by simp)
    obtain ⟨x, _hx, hxt⟩ := Finset.mem_map.mp (hsub htEdge)
    cases x with
    | inl u => exact Sum.inl_ne_inr hxt
    | inr r => exact r.2 (Sum.inr.inj hxt)

/-- The mapped private-child completion lies in the parent completion after
deleting the consumed ghost and live terminal. -/
theorem State.map_deletePrivate_completionEdges_subset_doubleDelete
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    mapEdgeSet (remainingPrivateCompletionEmbedding v t)
        (S.deletePrivate v t hOne hvt).completionEdges ⊆
      deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  have hAvoid := deletedPrivate_not_mem_mappedCompletionEdge v t g
  exact mem_deleteVertexEdges.mpr
    ⟨mem_deleteVertexEdges.mpr
      ⟨S.map_deletePrivate_completionEdges_subset v t hOne hvt
        (Finset.mem_map.mpr ⟨g, hg, rfl⟩), hAvoid.2⟩,
      hAvoid.1⟩

omit [Fintype V] [Fintype Flag] [DecidableEq Flag] in
/-- A restricted live response edge maps to its original lifted parent
edge even when the flag type is restricted simultaneously. -/
theorem map_lift_restrictSimpleEdge_private
    (v : V) (t : Flag) (e : SimpleEdge V) (hve : v ∉ e.vertices) :
    mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
        (liftLiveEdge (Flag := RemainingFlag t)
          (restrictSimpleEdge v e hve)) =
      liftLiveEdge (Flag := Flag) e := by
  rw [map_liftLiveEdge_private, map_restrictSimpleEdge]

/-- Insert a response edge whose addability has been certified in the
double-deleted parent completion.  The returned object is the literal
smaller flag state with a sparse completion. -/
theorem State.exists_insertedPrivateChild_of_addable
    (S : State V Flag) (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hfAbsent : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) f)
        (deleteVertexEdges
          (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)))) :
    ∃ heMissing : ∀ u : RemainingFlag t,
        restrictSimpleEdge v f hvf ≠
          (S.deletePrivate v t hOne hvt).missing u,
      ((S.deletePrivate v t hOne hvt).insertLiveEdge
        (restrictSimpleEdge v f hvf) heMissing).CompletionSparse := by
  have hfMissingParent : ∀ u : RemainingFlag t, f ≠ S.missing u.1 := by
    intro u hfu
    subst f
    exact hfAbsent (S.lifted_missing_mem_completionEdges u.1)
  have heMissing : ∀ u : RemainingFlag t,
      restrictSimpleEdge v f hvf ≠
        (S.deletePrivate v t hOne hvt).missing u := by
    intro u hEq
    apply hfMissingParent u
    have hmap := congrArg
      (mapSimpleEdge (remainingVertexEmbedding v)) hEq
    change mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v f hvf) =
      mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v (S.missing u.1)
          (private_not_mem_retained_missing_vertices
            S v t hOne hvt u)) at hmap
    simpa only [map_restrictSimpleEdge] using hmap
  refine ⟨heMissing, ?_⟩
  apply sparse22_of_mapEdgeSet_subset
    (remainingPrivateCompletionEmbedding v t) hSparse
  intro e he
  rw [(S.deletePrivate v t hOne hvt).completionEdges_insertLiveEdge] at he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  rw [Finset.mem_insert] at hg
  rcases hg with rfl | hgOld
  · change mapSimpleEdge (remainingPrivateCompletionEmbedding v t)
      (liftLiveEdge (Flag := RemainingFlag t)
        (restrictSimpleEdge v f hvf)) ∈ _
    rw [map_lift_restrictSimpleEdge_private]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (S.map_deletePrivate_completionEdges_subset_doubleDelete
        v t hOne hvt (Finset.mem_map.mpr ⟨g, hgOld, rfl⟩))

end ProvenanceFlag

end

end RB31E2E
