import RB31EndToEnd.Combinatorics.ProvenanceFlagDeletion
import RB31EndToEnd.Combinatorics.ProvenanceFlagInsertion
import RB31EndToEnd.Combinatorics.Sparse22.DegreeThreeAugmentation
import RB31EndToEnd.Linear.OutsideLocalGeometry

/-!
# The combinatorial outside move for provenance flags

An outside live vertex belongs to no active terminal triple.  Consequently
its incidence packet in the completed graph is exactly the lift of its live
incidence packet.  This file proves that equality and applies the arbitrary
sparse degree-three augmentation theorem to the literal completion.

The conclusion is deliberately stated in the completed graph.  It says
that the three lifted neighbours already span a complete triangle, or
returns a genuinely absent completion edge whose insertion after deleting
the outside vertex remains sparse.  Subsequent state constructors may then
either register the complete triangle as a new flag or transport the
addable edge to the outside child.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The canonical inclusion of live vertices into the completion. -/
def completionLiveEmbedding : V ↪ V ⊕ Flag where
  toFun := Sum.inl
  inj' := Sum.inl_injective

omit [Fintype V] [Fintype Flag] in
@[simp]
theorem inl_mem_liftLiveEdge_vertices
    (v : V) (e : SimpleEdge V) :
    Sum.inl v ∈ (liftLiveEdge (Flag := Flag) e).vertices ↔
      v ∈ e.vertices := by
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [liftLiveEdge, SimpleEdge.vertices]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem liftLiveEdge_eq_mapSimpleEdge (e : SimpleEdge V) :
    liftLiveEdge (Flag := Flag) e =
      Sparse22Transport.mapSimpleEdge
        (completionLiveEmbedding (V := V) (Flag := Flag)) e := by
  rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- Lifting a named live pair is the identically named pair of left-sum
vertices. -/
theorem liftLiveEdge_simpleEdge
    (a b : V) (hab : a ≠ b) :
    liftLiveEdge (Flag := Flag) (simpleEdge a b hab) =
      simpleEdge (Sum.inl a) (Sum.inl b) (by simpa using hab) := by
  rfl

/-- At an outside vertex the completed incidence packet contains no
restored flag edge and no ghost-star edge. -/
theorem State.incidentEdges_completion_outside
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    incidentEdges S.completionEdges (Sum.inl v) =
      (incidentEdges S.edges v).map
        (liftLiveEdgeEmbedding (V := V) (Flag := Flag)) := by
  ext e
  constructor
  · intro he
    have heData := mem_incidentEdges.mp he
    rw [State.completionEdges] at heData
    rcases Finset.mem_union.mp heData.1 with heLM | heGhost
    · rcases Finset.mem_union.mp heLM with heLive | heMissing
      · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
        apply Finset.mem_map.mpr
        refine ⟨f, ?_, rfl⟩
        exact mem_incidentEdges.mpr
          ⟨hf, (inl_mem_liftLiveEdge_vertices
            (Flag := Flag) v f).1 heData.2⟩
      · obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
        subst e
        have hvMissing : v ∈ (S.missing t).vertices :=
          (inl_mem_liftLiveEdge_vertices
            (Flag := Flag) v (S.missing t)).1 heData.2
        exact (outside_not_mem_missing_vertices S v hv t hvMissing).elim
    · obtain ⟨t, _ht, heStar⟩ := Finset.mem_biUnion.mp heGhost
      obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp heStar
      subst e
      have hvu : v = u := by
        simpa [vertices_ghostEdge] using heData.2
      subst u
      exact (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t hu).elim
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    apply mem_incidentEdges.mpr
    constructor
    · apply S.liftedLiveEdges_subset_completionEdges
      exact Finset.mem_map.mpr
        ⟨f, (mem_incidentEdges.mp hf).1, rfl⟩
    · exact (inl_mem_liftLiveEdge_vertices
        (Flag := Flag) v f).2 (mem_incidentEdges.mp hf).2

/-- In particular, live degree and completed degree agree at an outside
vertex. -/
theorem State.edgeSetDegree_completion_outside
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    edgeSetDegree S.completionEdges (Sum.inl v) =
      edgeSetDegree S.edges v := by
  rw [edgeSetDegree, S.incidentEdges_completion_outside v hv,
    Finset.card_map]
  rfl

/-- Lift a named degree-three neighbour packet from the live graph to the
literal completion. -/
def liftDegreeThreeNeighbours
    (S : State V Flag) {v : V}
    (N : DirectionStress.DegreeThreeNeighbours S.edges v) :
    DirectionStress.DegreeThreeNeighbours S.completionEdges (Sum.inl v) where
  p := Sum.inl N.p
  q := Sum.inl N.q
  r := Sum.inl N.r
  hvp := by simp [N.hvp]
  hvq := by simp [N.hvq]
  hvr := by simp [N.hvr]
  hpq := by simp [N.hpq]
  hpr := by simp [N.hpr]
  hqr := by simp [N.hqr]
  vp_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.p N.hvp) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vp_mem
  vq_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.q N.hvq) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vq_mem
  vr_mem := by
    change liftLiveEdge (Flag := Flag) (simpleEdge v N.r N.hvr) ∈
      S.completionEdges
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact N.vr_mem

/-- The exact complete-or-addable alternative in the completed graph at
an outside degree-three vertex. -/
theorem State.outside_neighbour_triangle_complete_or_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    let Nhat := liftDegreeThreeNeighbours S N
    (simpleEdge Nhat.p Nhat.q Nhat.hpq ∈ S.completionEdges ∧
        simpleEdge Nhat.p Nhat.r Nhat.hpr ∈ S.completionEdges ∧
        simpleEdge Nhat.q Nhat.r Nhat.hqr ∈ S.completionEdges) ∨
      ∃ e : SimpleEdge (V ⊕ Flag),
        e ∈ ({simpleEdge Nhat.p Nhat.q Nhat.hpq,
            simpleEdge Nhat.p Nhat.r Nhat.hpr,
            simpleEdge Nhat.q Nhat.r Nhat.hqr} :
              SimpleEdgeSet (V ⊕ Flag)) ∧
        e ∉ S.completionEdges ∧
        Sparse22
          (insert e
            (deleteVertexEdges S.completionEdges (Sum.inl v))) := by
  let Nhat := liftDegreeThreeNeighbours S N
  have hDegreeHat : edgeSetDegree S.completionEdges (Sum.inl v) = 3 := by
    rw [S.edgeSetDegree_completion_outside v hv]
    exact hDegree
  simpa only [Nhat] using
    (degree_three_neighbour_triangle_complete_or_addable
      (F := S.completionEdges) (v := Sum.inl v)
      (a := Nhat.p) (b := Nhat.q) (c := Nhat.r)
      hSparse Nhat.hvp Nhat.hvq Nhat.hvr
      Nhat.hpq Nhat.hpr Nhat.hqr hDegreeHat
      Nhat.vp_mem Nhat.vq_mem Nhat.vr_mem)

/-- The same alternative with an addable edge returned in the original
live vertex type. -/
theorem State.outside_live_neighbour_triangle_complete_or_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    (liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) ∨
      ∃ f : SimpleEdge V,
        f ∈ ({simpleEdge N.p N.q N.hpq,
            simpleEdge N.p N.r N.hpr,
            simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V) ∧
        liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
        Sparse22
          (insert (liftLiveEdge (Flag := Flag) f)
            (deleteVertexEdges S.completionEdges (Sum.inl v))) := by
  rcases S.outside_neighbour_triangle_complete_or_addable
      hSparse v hv N hDegree with hComplete | hAdd
  · left
    simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using hComplete
  · obtain ⟨e, heTriangle, heAbsent, heSparse⟩ := hAdd
    simp only [Finset.mem_insert, Finset.mem_singleton] at heTriangle
    rcases heTriangle with he | he | he
    · subst e
      refine Or.inr ⟨simpleEdge N.p N.q N.hpq, by simp, ?_, ?_⟩
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse
    · subst e
      refine Or.inr ⟨simpleEdge N.p N.r N.hpr, by simp, ?_, ?_⟩
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse
    · subst e
      refine Or.inr ⟨simpleEdge N.q N.r N.hqr, by simp, ?_, ?_⟩
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heAbsent
      · simpa [liftDegreeThreeNeighbours, liftLiveEdge_simpleEdge] using heSparse

/-- A mapped edge of the outside child cannot meet the deleted live vertex
in the parent completion. -/
theorem deletedOutside_not_mem_mappedCompletionEdge
    (v : V) (e : SimpleEdge (RemainingVertex v ⊕ Flag)) :
    Sum.inl v ∉
      (Sparse22Transport.mapSimpleEdge
        (remainingCompletionEmbedding (Flag := Flag) v) e).vertices := by
  intro hvEdge
  have hsub := Sparse22Transport.mapSimpleEdge_vertices_subset
    (remainingCompletionEmbedding (Flag := Flag) v) e
    (Finset.univ : Finset (RemainingVertex v ⊕ Flag)) (by simp)
  have hvRange := hsub hvEdge
  obtain ⟨x, _hx, hxv⟩ := Finset.mem_map.mp hvRange
  cases x with
  | inl u =>
      change Sum.inl (u.1 : V) = Sum.inl v at hxv
      exact u.2 (Sum.inl.inj hxv)
  | inr t =>
      change Sum.inr t = Sum.inl v at hxv
      exact Sum.inr_ne_inl hxv

/-- The mapped outside-child completion lies in the parent completion with
the deleted live vertex removed. -/
theorem State.map_deleteOutside_completionEdges_subset_delete
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0) :
    Sparse22Transport.mapEdgeSet
        (remainingCompletionEmbedding (Flag := Flag) v)
        (S.deleteOutside v hv).completionEdges ⊆
      deleteVertexEdges S.completionEdges (Sum.inl v) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  exact mem_deleteVertexEdges.mpr
    ⟨map_deleteOutside_completionEdges_subset S v hv
        (Finset.mem_map.mpr ⟨g, hg, rfl⟩),
      deletedOutside_not_mem_mappedCompletionEdge v g⟩

omit [Fintype V] [Fintype Flag] [DecidableEq Flag] in
/-- Mapping a lifted restricted live edge into the parent completion
recovers the original lifted live edge. -/
theorem map_lift_restrictSimpleEdge_remaining
    (v : V) (e : SimpleEdge V) (hve : v ∉ e.vertices) :
    Sparse22Transport.mapSimpleEdge
        (remainingCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag) (restrictSimpleEdge v e hve)) =
      liftLiveEdge (Flag := Flag) e := by
  calc
    _ = liftLiveEdge (Flag := Flag)
          (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
            (restrictSimpleEdge v e hve)) := by
      apply Subtype.ext
      simp only [Sparse22Transport.mapSimpleEdge_val, liftLiveEdge_val,
        Sym2.map_map]
      induction (restrictSimpleEdge v e hve).1 using Sym2.inductionOn with
      | _ a b =>
          simp [remainingCompletionEmbedding, remainingVertexEmbedding]
    _ = liftLiveEdge (Flag := Flag) e := by
      rw [map_restrictSimpleEdge]

/-- Insert a certified addable completion edge into the outside child.
The child state and its sparse completion are constructed literally. -/
theorem State.exists_insertedOutsideChild_of_addable
    (S : State V Flag) (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hfAbsent : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) f)
        (deleteVertexEdges S.completionEdges (Sum.inl v)))) :
    ∃ heMissing : ∀ t : Flag,
        restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t,
      ((S.deleteOutside v hv).insertLiveEdge
        (restrictSimpleEdge v f hvf) heMissing).CompletionSparse := by
  have hfMissingParent : ∀ t : Flag, f ≠ S.missing t := by
    intro t hft
    subst f
    exact hfAbsent (S.lifted_missing_mem_completionEdges t)
  have heMissing : ∀ t : Flag,
      restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t := by
    intro t hEq
    apply hfMissingParent t
    have hmap := congrArg
      (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)) hEq
    change Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v f hvf) =
      Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (restrictSimpleEdge v (S.missing t)
          (outside_not_mem_missing_vertices S v hv t)) at hmap
    simpa only [map_restrictSimpleEdge] using hmap
  refine ⟨heMissing, ?_⟩
  apply Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (remainingCompletionEmbedding (Flag := Flag) v) hSparse
  intro e he
  rw [(S.deleteOutside v hv).completionEdges_insertLiveEdge] at he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  rw [Finset.mem_insert] at hg
  rcases hg with rfl | hgOld
  · change Sparse22Transport.mapSimpleEdge
      (remainingCompletionEmbedding (Flag := Flag) v)
      (liftLiveEdge (Flag := Flag) (restrictSimpleEdge v f hvf)) ∈ _
    rw [map_lift_restrictSimpleEdge_remaining]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (S.map_deleteOutside_completionEdges_subset_delete v hv
        (Finset.mem_map.mpr ⟨g, hgOld, rfl⟩))

omit [Fintype V] in
/-- Every neighbour-pair returned by a named degree-three packet avoids
the apex. -/
theorem not_mem_degreeThreeNeighbourPair
    {F : SimpleEdgeSet V} {v : V}
    (N : DirectionStress.DegreeThreeNeighbours F v)
    (f : SimpleEdge V)
    (hf : f ∈ ({simpleEdge N.p N.q N.hpq,
      simpleEdge N.p N.r N.hpr,
      simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V)) :
    v ∉ f.vertices := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl <;>
    simp [vertices_simpleEdge, N.hvp, N.hvq, N.hvr]

/-- Outside complete-or-addable transition with the addable branch already
packaged as an actual smaller sparse flag state. -/
theorem State.outside_complete_or_exists_sparse_insertedChild
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hDegree : edgeSetDegree S.edges v = 3) :
    (liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) ∨
      ∃ (f : SimpleEdge V)
          (hfTriangle : f ∈ ({simpleEdge N.p N.q N.hpq,
            simpleEdge N.p N.r N.hpr,
            simpleEdge N.q N.r N.hqr} : SimpleEdgeSet V))
          (heMissing : ∀ t : Flag,
            restrictSimpleEdge v f
                (not_mem_degreeThreeNeighbourPair N f hfTriangle) ≠
              (S.deleteOutside v hv).missing t),
        liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
          ((S.deleteOutside v hv).insertLiveEdge
            (restrictSimpleEdge v f
              (not_mem_degreeThreeNeighbourPair N f hfTriangle))
            heMissing).CompletionSparse := by
  rcases S.outside_live_neighbour_triangle_complete_or_addable
      hSparse v hv N hDegree with hComplete | hAdd
  · exact Or.inl hComplete
  · obtain ⟨f, hfTriangle, hfAbsent, hfSparse⟩ := hAdd
    let hvf := not_mem_degreeThreeNeighbourPair N f hfTriangle
    obtain ⟨heMissing, hChildSparse⟩ :=
      S.exists_insertedOutsideChild_of_addable
        v hv f hvf hfAbsent hfSparse
    exact Or.inr ⟨f, hfTriangle, heMissing, hfAbsent, hChildSparse⟩

end ProvenanceFlag

end

end RB31E2E
