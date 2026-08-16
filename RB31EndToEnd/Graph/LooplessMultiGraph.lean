import Mathlib

/-!
# Finite loopless multigraphs with occurrence-level edges

`SimpleGraph` deliberately forgets parallel-edge provenance.  The structure in
this file keeps an independent finite type of edge occurrences, and supplies an
underlying simple graph only as a derived object.
-/

namespace RB31E2E

/--
A finite loopless multigraph whose parallel edges remain distinct inhabitants
of `Edge`.  The endpoint order is bookkeeping only: all graph-level predicates
below treat the endpoints as unordered.
-/
structure LooplessMultiGraph where
  Vertex : Type
  Edge : Type
  vertexFinite : Fintype Vertex
  edgeFinite : Fintype Edge
  vertexDecidableEq : DecidableEq Vertex
  edgeDecidableEq : DecidableEq Edge
  source : Edge → Vertex
  target : Edge → Vertex
  loopless : ∀ e, source e ≠ target e

attribute [instance] LooplessMultiGraph.vertexFinite
attribute [instance] LooplessMultiGraph.edgeFinite
attribute [instance] LooplessMultiGraph.vertexDecidableEq
attribute [instance] LooplessMultiGraph.edgeDecidableEq

namespace LooplessMultiGraph

/-- An occurrence has the unordered endpoint pair `{v,w}`. -/
def HasEndpoints (G : LooplessMultiGraph) (e : G.Edge) (v w : G.Vertex) : Prop :=
  (G.source e = v ∧ G.target e = w) ∨
    (G.source e = w ∧ G.target e = v)

theorem hasEndpoints_comm (G : LooplessMultiGraph) (e : G.Edge) (v w : G.Vertex) :
    G.HasEndpoints e v w ↔ G.HasEndpoints e w v := by
  simp only [HasEndpoints, or_comm]

/-- The finite set of edge occurrences between two vertices. -/
noncomputable def edgesBetween (G : LooplessMultiGraph) (v w : G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e ↦ G.HasEndpoints e v w

theorem edgesBetween_comm (G : LooplessMultiGraph) (v w : G.Vertex) :
    G.edgesBetween v w = G.edgesBetween w v := by
  classical
  ext e
  simp [edgesBetween, HasEndpoints, or_comm]

/-- The number of edge occurrences between two vertices. -/
noncomputable def multiplicity (G : LooplessMultiGraph) (v w : G.Vertex) : ℕ :=
  (G.edgesBetween v w).card

theorem multiplicity_comm (G : LooplessMultiGraph) (v w : G.Vertex) :
    G.multiplicity v w = G.multiplicity w v := by
  rw [multiplicity, multiplicity, G.edgesBetween_comm v w]

theorem no_edge_has_equal_endpoints (G : LooplessMultiGraph) (e : G.Edge) (v : G.Vertex) :
    ¬ G.HasEndpoints e v v := by
  intro h
  rcases h with h | h <;> exact G.loopless e (h.1.trans h.2.symm)

@[simp] theorem edgesBetween_self (G : LooplessMultiGraph) (v : G.Vertex) :
    G.edgesBetween v v = ∅ := by
  classical
  ext e
  simp [edgesBetween, G.no_edge_has_equal_endpoints e v]

@[simp] theorem multiplicity_self (G : LooplessMultiGraph) (v : G.Vertex) :
    G.multiplicity v v = 0 := by
  simp [multiplicity]

/-- Forget parallel-edge multiplicity while retaining adjacency. -/
def underlyingSimpleGraph (G : LooplessMultiGraph) : SimpleGraph G.Vertex where
  Adj v w := ∃ e, G.HasEndpoints e v w
  symm := by
    intro v w h
    rcases h with ⟨e, he⟩
    exact ⟨e, (G.hasEndpoints_comm e v w).mp he⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨e, he⟩
    exact G.no_edge_has_equal_endpoints e v he⟩

theorem underlyingSimpleGraph_adj_iff (G : LooplessMultiGraph) (v w : G.Vertex) :
    G.underlyingSimpleGraph.Adj v w ↔ ∃ e, G.HasEndpoints e v w :=
  Iff.rfl

theorem underlyingSimpleGraph_adj_iff_multiplicity_pos
    (G : LooplessMultiGraph) (v w : G.Vertex) :
    G.underlyingSimpleGraph.Adj v w ↔ 0 < G.multiplicity v w := by
  classical
  constructor
  · rintro ⟨e, he⟩
    rw [multiplicity, Finset.card_pos]
    exact ⟨e, by simp [edgesBetween, he]⟩
  · intro h
    rw [multiplicity, Finset.card_pos] at h
    rcases h with ⟨e, he⟩
    exact ⟨e, by simpa [edgesBetween] using he⟩

end LooplessMultiGraph

end RB31E2E
