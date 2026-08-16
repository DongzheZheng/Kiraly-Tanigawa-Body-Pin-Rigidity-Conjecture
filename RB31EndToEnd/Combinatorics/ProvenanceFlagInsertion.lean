import RB31EndToEnd.Combinatorics.ProvenanceFlag

/-!
# Inserting a certified live response edge into a flag state

When a virtual response row is available, the flag induction inserts its
underlying live edge.  The only compatibility condition is that the edge is
not the distinguished missing edge of any retained flag.  This file builds
the resulting `State` literally and identifies its completion with insertion
of the lifted edge into the old completion.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Insert one live edge while retaining all active flag data. -/
def State.insertLiveEdge (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) : State V Flag where
  edges := insert e S.edges
  terminals := S.terminals
  missing := S.missing
  terminals_card := S.terminals_card
  missing_supported := S.missing_supported
  missing_not_live t := by
    simp [S.missing_not_live t, Ne.symm (heMissing t)]
  other_terminal_edges_live t f hfT hfMissing := by
    exact Finset.mem_insert_of_mem
      (S.other_terminal_edges_live t f hfT hfMissing)

@[simp]
theorem State.insertLiveEdge_edges
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (S.insertLiveEdge e heMissing).edges = insert e S.edges := rfl

@[simp]
theorem State.insertLiveEdge_terminals
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) (t : Flag) :
    (S.insertLiveEdge e heMissing).terminals t = S.terminals t := rfl

@[simp]
theorem State.insertLiveEdge_missing
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) (t : Flag) :
    (S.insertLiveEdge e heMissing).missing t = S.missing t := rfl

/-- The literal completion changes by exactly the lifted inserted edge. -/
theorem State.completionEdges_insertLiveEdge
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (S.insertLiveEdge e heMissing).completionEdges =
      insert (liftLiveEdge (Flag := Flag) e) S.completionEdges := by
  rw [State.completionEdges, State.completionEdges]
  have hLift :
      (S.insertLiveEdge e heMissing).liftedLiveEdges =
        insert (liftLiveEdge (Flag := Flag) e) S.liftedLiveEdges := by
    ext f
    simp [State.liftedLiveEdges, liftLiveEdgeEmbedding]
  have hMissing :
      (S.insertLiveEdge e heMissing).restoredMissingEdges =
        S.restoredMissingEdges := by
    rfl
  have hGhost :
      (S.insertLiveEdge e heMissing).ghostStarEdges =
        S.ghostStarEdges := by
    rfl
  rw [hLift, hMissing, hGhost]
  ext f
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- A sparse certified insertion into the completion produces a sparse
child flag state. -/
theorem State.insertLiveEdge_completionSparse
    (S : State V Flag) (e : SimpleEdge V)
    (heMissing : ∀ t : Flag, e ≠ S.missing t)
    (hSparse : Sparse22
      (insert (liftLiveEdge (Flag := Flag) e) S.completionEdges)) :
    (S.insertLiveEdge e heMissing).CompletionSparse := by
  rw [State.CompletionSparse, S.completionEdges_insertLiveEdge]
  exact hSparse

end ProvenanceFlag

end

end RB31E2E
