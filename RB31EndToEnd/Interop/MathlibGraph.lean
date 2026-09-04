import RB31EndToEnd.Rigidity.BodyPinGraph
import Mathlib.Combinatorics.Graph.Basic

/-!
# Interoperability with mathlib multigraphs

The body--pin input keeps each pin occurrence as a separate edge.  This file
exports that data through mathlib's edge-indexed `Graph` interface, used by
other Lean rigidity developments for body--bar graphs.  The expanded
bar--joint graph remains a `SimpleGraph`.
-/

namespace RB31E2E

namespace LooplessMultiGraph

/-- The edge-indexed mathlib graph underlying a finite loopless multigraph.
Every vertex and every edge occurrence is active. -/
def toGraph (G : LooplessMultiGraph) : Graph G.Vertex G.Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e v w := G.HasEndpoints e v w
  isLink_symm := by
    intro e _ v w h
    exact (G.hasEndpoints_comm e v w).mp h
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases hxy with hxy | hxy <;> rcases hvw with hvw | hvw
    · exact Or.inl (hxy.1.symm.trans hvw.1)
    · exact Or.inr (hxy.1.symm.trans hvw.1)
    · exact Or.inr (hxy.2.symm.trans hvw.2)
    · exact Or.inl (hxy.2.symm.trans hvw.2)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      exact ⟨G.source e, G.target e, Or.inl ⟨rfl, rfl⟩⟩
    · intro _
      exact Set.mem_univ e
  left_mem_of_isLink := by
    intro e v w h
    exact Set.mem_univ v

@[simp]
theorem toGraph_vertexSet (G : LooplessMultiGraph) : G.toGraph.vertexSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_edgeSet (G : LooplessMultiGraph) : G.toGraph.edgeSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_isLink_iff (G : LooplessMultiGraph) (e : G.Edge) (v w : G.Vertex) :
    G.toGraph.IsLink e v w ↔ G.HasEndpoints e v w :=
  Iff.rfl

@[simp]
theorem toGraph_adj_iff (G : LooplessMultiGraph) (v w : G.Vertex) :
    G.toGraph.Adj v w ↔ G.underlyingSimpleGraph.Adj v w :=
  Iff.rfl

@[simp]
theorem not_toGraph_isLoopAt (G : LooplessMultiGraph) (e : G.Edge) (v : G.Vertex) :
    ¬ G.toGraph.IsLoopAt e v :=
  G.no_edge_has_equal_endpoints e v

/-- Edge occurrences are unchanged by `toGraph`; the subtype only certifies
membership in the full edge set. -/
def edgeEquiv (G : LooplessMultiGraph) : G.Edge ≃ G.toGraph.edgeSet where
  toFun e := ⟨e, Set.mem_univ e⟩
  invFun e := e.1
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem edgeEquiv_apply_coe (G : LooplessMultiGraph) (e : G.Edge) :
    (G.edgeEquiv e : G.Edge) = e :=
  rfl

end LooplessMultiGraph

namespace BodyPinIncidence

/-- The body--pin incidence multigraph in mathlib's edge-indexed `Graph`
interface.  Parallel pins remain distinct elements of `H.Pin`. -/
def toGraph (H : BodyPinIncidence) : Graph H.Body H.Pin :=
  H.toLooplessMultiGraph.toGraph

@[simp]
theorem toGraph_vertexSet (H : BodyPinIncidence) : H.toGraph.vertexSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_edgeSet (H : BodyPinIncidence) : H.toGraph.edgeSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_isLink_iff (H : BodyPinIncidence) (e : H.Pin) (u v : H.Body) :
    H.toGraph.IsLink e u v ↔
      (H.left e = u ∧ H.right e = v) ∨
        (H.left e = v ∧ H.right e = u) :=
  Iff.rfl

@[simp]
theorem toGraph_adj_iff (H : BodyPinIncidence) (u v : H.Body) :
    H.toGraph.Adj u v ↔ H.toLooplessMultiGraph.underlyingSimpleGraph.Adj u v :=
  Iff.rfl

@[simp]
theorem not_toGraph_isLoopAt (H : BodyPinIncidence) (e : H.Pin) (u : H.Body) :
    ¬ H.toGraph.IsLoopAt e u :=
  H.toLooplessMultiGraph.no_edge_has_equal_endpoints e u

/-- The pin type is canonically equivalent to the edge set of `H.toGraph`. -/
def pinEquiv (H : BodyPinIncidence) : H.Pin ≃ H.toGraph.edgeSet :=
  H.toLooplessMultiGraph.edgeEquiv

@[simp]
theorem pinEquiv_apply_coe (H : BodyPinIncidence) (e : H.Pin) :
    (H.pinEquiv e : H.Pin) = e :=
  rfl

end BodyPinIncidence

end RB31E2E
