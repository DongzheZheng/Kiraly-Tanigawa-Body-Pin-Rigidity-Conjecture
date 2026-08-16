import RB31EndToEnd.NullCellule.ProvenanceFlagOutsideExceptionalBudget
import RB31EndToEnd.Combinatorics.ProvenanceFlagOutsideMove

/-!
# Closing the outside exceptional induction move

The full-response theorem supplies the actual degree-three neighbour
packet.  Completion sparsity then gives a complete-or-addable alternative.
Both alternatives construct literal smaller sparse states, so the supplied
strong-induction hypothesis is applied only to genuinely smaller live types.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The outside exceptional step.  The response rows and numerical
equalities follow from the local classification and coefficient descent. -/
theorem FunctionFieldBranch.semismallBudget_of_outsideExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V)
    (hSparse : S.CompletionSparse)
    (hv : S.flagMultiplicity v = 0)
    (hDegree : edgeSetDegree S.edges v ≤ 3)
    (hSmaller :
      ∀ {K' : Type v} {V' : Type w} {Flag' : Type x}
        [Field K'] [Algebra k K']
        [Fintype V'] [DecidableEq V'] [Fintype Flag'] [DecidableEq Flag'],
        Fintype.card V' < Fintype.card V →
          ∀ (S' : State V' Flag')
            (Y' : FunctionFieldBranch (k := k) (K := K') S'),
            S'.CompletionSparse → Y'.SemismallBudget S')
    (hExceptional : OutsideExceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  obtain ⟨N, hDegreeThree, hTrdegThree, hResponseOne, hcol,
      hpqRow, hprRow, hqrRow⟩ :=
    outsideExceptional_fullResponse (k := k)
      S.edges Y.position v Y.distinct hDegree Y.generated hExceptional
  rcases S.outside_complete_or_exists_sparse_insertedChild
      hSparse v hv N hDegreeThree with hComplete | hAddable
  · have hTriangleLive :=
      S.outside_complete_triangle_live hSparse v hv N hComplete
    let registered := S.registerOutside hSparse v hv N hTriangleLive
    let child := Y.registerOutsideIntrinsic
      S hSparse v hv N hTriangleLive hcol
    have hCard : Fintype.card (RemainingVertex v) < Fintype.card V := by
      have hDrop := card_remainingVertex_add_one v
      omega
    have hChild : child.SemismallBudget registered := by
      exact hSmaller hCard registered child
        (S.registerOutside_completionSparse
          hSparse v hv N hTriangleLive)
    exact Y.semismallBudget_of_registerOutsideIntrinsic
      S hSparse v hv N hTriangleLive hcol hResponseOne hTrdegThree hChild
  · obtain ⟨f, hfTriangle, heMissing, hfAbsent, hChildSparse⟩ := hAddable
    let hvf := not_mem_degreeThreeNeighbourPair N f hfTriangle
    have hfLive : f ∉ S.edges := outside_addable_edge_not_live S f hfAbsent
    have hfDeleted : f ∉ deleteVertexEdges S.edges v := by
      intro h
      exact hfLive (mem_deleteVertexEdges.mp h).1
    have hrow : directionRow Y.position f ∈
        directionRowSpace (deleteVertexEdges S.edges v) Y.position := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfTriangle
      rcases hfTriangle with rfl | rfl | rfl
      · exact hpqRow
      · exact hprRow
      · exact hqrRow
    let childState := (S.deleteOutside v hv).insertLiveEdge
      (restrictSimpleEdge v f hvf) heMissing
    let childBase := Y.deleteOutsideIntrinsic S v hv
    let child := childBase.insertLiveEdge
      (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing
    have hCard : Fintype.card (RemainingVertex v) < Fintype.card V := by
      have hDrop := card_remainingVertex_add_one v
      omega
    have hChild : child.SemismallBudget childState := by
      exact hSmaller hCard childState child hChildSparse
    exact Y.semismallBudget_of_outsideInsertedIntrinsic
      S v hv f hvf heMissing hfDeleted hrow hResponseOne hTrdegThree hChild

end ProvenanceFlag

end

end RB31E2E
