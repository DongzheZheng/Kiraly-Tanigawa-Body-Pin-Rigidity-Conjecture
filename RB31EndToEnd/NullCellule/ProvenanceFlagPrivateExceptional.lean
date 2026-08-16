import RB31EndToEnd.Combinatorics.ProvenanceFlagPrivatePivot
import RB31EndToEnd.Linear.PrivatePivotStress
import RB31EndToEnd.Linear.DirectionResponseVertexDeletion
import RB31EndToEnd.NullCellule.ProvenanceFlagInsertedBranch
import RB31EndToEnd.NullCellule.ProvenanceFlagSemismallness

/-!
# Closing the private exceptional induction move

This file first transports a function-field branch across the literal
completion-preserving private pivot.  The pivot changes neither the
coordinates nor the flag triples, and collinearity makes its one-for-one
live-edge exchange preserve direction-stress dimension.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The unchanged coordinate branch on the oriented private-pivot state. -/
def FunctionFieldBranch.privatePivot
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    FunctionFieldBranch (k := k) (K := K) D.state where
  position := Y.position
  generated := Y.generated
  distinct := Y.distinct
  collinear r := by
    rw [D.terminals_eq]
    exact Y.collinear r

@[simp]
theorem FunctionFieldBranch.privatePivot_position
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    (Y.privatePivot S hSparse D).position = Y.position := rfl

/-- The pivoted branch has exactly the original direction-stress
dimension.  In the nontrivial gauge this is the collinear triangle row
exchange theorem, applied to facts reconstructed from the literal state. -/
theorem FunctionFieldBranch.privatePivot_stressDim_eq
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt) :
    (Y.privatePivot S hSparse D).stressDim D.state = Y.stressDim S := by
  change directionStressDim D.state.edges Y.position =
    directionStressDim S.edges Y.position
  rcases D.pivoted with hState | ⟨hvqLive, hPQMissing, hState⟩
  · rw [hState]
  · rw [hState]
    apply directionStressDim_exchange_collinear_triangle
      S.edges Y.position v D.p D.q D.hvp D.hvq D.hpq
    · apply S.other_terminal_edges_live t _
      · rw [vertices_simpleEdge, D.original_terminals]
        simp
      · rw [hPQMissing]
        simp [simpleEdge_eq_simpleEdge_iff, D.hvp, D.hvq, D.hpq]
    · exact hvqLive
    · rw [← hPQMissing]
      exact S.missing_not_live t
    · exact Y.distinct
    · apply pinCollinear_of_affinelyCollinearOn
        Y.position (S.terminals t) v D.p D.q (Y.collinear t)
      · rw [D.original_terminals]
        simp
      · rw [D.original_terminals]
        simp
      · rw [D.original_terminals]
        simp

/-- A semismall budget on an oriented pivot state transfers back to the
original state because the function field, live and flag types, and stress
dimension are unchanged. -/
theorem FunctionFieldBranch.semismallBudget_of_privatePivot
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (hSparse : S.CompletionSparse)
    (D : PrivatePivotData S hSparse v t hOne hvt)
    (hPivot : (Y.privatePivot S hSparse D).SemismallBudget D.state) :
    Y.SemismallBudget S := by
  unfold FunctionFieldBranch.SemismallBudget at hPivot ⊢
  rw [Y.privatePivot_stressDim_eq S hSparse D] at hPivot
  exact hPivot

/-! ## The inserted-child exceptional ledger -/

/-- In the classified private exceptional shape, a virtual response edge
inserted into the intrinsic private child restores exactly the parent's
one lost stress.  Its recursive budget therefore lifts to the parent: the
extension degree contributes one and consuming the flag contributes two,
exactly matching the three coordinates of the deleted vertex. -/
theorem FunctionFieldBranch.semismallBudget_of_insertedPrivateExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices) (hf : f ∉ S.edges)
    (heMissing : ∀ r : RemainingFlag t,
      restrictSimpleEdge v f hvf ≠
        (S.deletePrivate v t hOne hvt).missing r)
    (hExtension : outsideExtensionTrdeg (k := k) Y.position v = 1)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hRow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hChild :
      ((Y.deletePrivateIntrinsic S v t hOne hvt).insertLiveEdge
          (S.deletePrivate v t hOne hvt)
          (restrictSimpleEdge v f hvf) heMissing).SemismallBudget
        ((S.deletePrivate v t hOne hvt).insertLiveEdge
          (restrictSimpleEdge v f hvf) heMissing)) :
    Y.SemismallBudget S := by
  let child := S.deletePrivate v t hOne hvt
  let e := restrictSimpleEdge v f hvf
  let Z := Y.deletePrivateIntrinsic S v t hOne hvt
  let inserted := child.insertLiveEdge e heMissing
  let Zi := Z.insertLiveEdge child e heMissing
  have hfDeleted : f ∉ deleteVertexEdges S.edges v := by
    intro hmem
    exact hf (mem_deleteVertexEdges.mp hmem).1
  have heAbsent : e ∉ restrictedLiveEdges S.edges v := by
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hfDeleted hmem
  have hRowIntrinsic :
      directionRow
          (intrinsicRestrictedPlacement (k := k) Y.position v) e ∈
        directionRowSpace (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) := by
    dsimp only [e]
    exact directionRow_intrinsicRestricted_mem_of_deleted_mem
      (L := k) S.edges Y.position v f hvf hfDeleted hRow
  have hAugment := directionStressDim_insert_eq_add_one_of_row_mem
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    e heAbsent hRowIntrinsic
  have hParentStress :=
    directionStressDim_eq_delete_add_outsideResponseKernelDim
      S.edges Y.position v
  rw [hResponse] at hParentStress
  have hStress : Zi.stressDim inserted = Y.stressDim S := by
    calc
      Zi.stressDim inserted =
          directionStressDim
            (insert e (restrictedLiveEdges S.edges v))
            (intrinsicRestrictedPlacement (k := k) Y.position v) := rfl
      _ = directionStressDim (restrictedLiveEdges S.edges v)
            (intrinsicRestrictedPlacement (k := k) Y.position v) + 1 :=
        hAugment
      _ = directionStressDim (deleteVertexEdges S.edges v) Y.position + 1 := by
        rw [directionStressDim_intrinsicRestrictedPlacement]
      _ = Y.stressDim S := hParentStress.symm
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  rw [hExtension] at hTower
  have hFlagCard := card_remainingFlag_add_one t
  have hFlagCardC :
      (Fintype.card (RemainingFlag t) : Cardinal) + 1 =
        (Fintype.card Flag : Cardinal) := by
    exact_mod_cast hFlagCard
  have hVertexCard := card_remainingVertex_add_one v
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (Y.stressDim S : Cardinal) + Algebra.trdeg k K +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (Y.stressDim S : Cardinal) + Algebra.trdeg k K +
          2 * (Fintype.card Flag : Cardinal) =
        ((Zi.stressDim inserted : Cardinal) +
            Algebra.trdeg k
              (retainedLiveCoordinateField (k := k) Y.position v) +
            2 * (Fintype.card (RemainingFlag t) : Cardinal)) + 3 := by
      rw [hStress, ← hTower, ← hFlagCardC]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      add_le_add hChild (le_refl 3)
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 =
          3 * Fintype.card V)

/-! ## The private exceptional step -/

/-- The private exceptional induction step.  Its premises describe the
selected private low-degree branch and the induction hypothesis on smaller
live types.  After orienting the unique flag, the proof rechecks the local
inequality on the pivoted state. -/
theorem FunctionFieldBranch.semismallBudget_of_privateExceptional
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hSparse : S.CompletionSparse)
    (hOne : S.flagMultiplicity v = 1)
    (hvt : v ∈ S.terminals t)
    (hDegree : edgeSetDegree S.edges v ≤ 2)
    (hSmaller :
      ∀ {K' : Type v} {V' : Type w} {Flag' : Type x}
        [Field K'] [Algebra k K']
        [Fintype V'] [DecidableEq V']
        [Fintype Flag'] [DecidableEq Flag'],
        Fintype.card V' < Fintype.card V →
          ∀ (S' : State V' Flag')
            (Y' : FunctionFieldBranch (k := k) (K := K') S'),
            S'.CompletionSparse → Y'.SemismallBudget S')
    (_hExceptional : PrivateExceptional (k := k) S.edges Y.position v) :
    Y.SemismallBudget S := by
  let D : PrivatePivotData S hSparse v t hOne hvt :=
    Classical.choice (S.exists_privatePivotData hSparse v t hOne hvt)
  let P := D.state
  let Yp := Y.privatePivot S hSparse D
  have hDegreeP : edgeSetDegree P.edges v ≤ 2 :=
    D.degree_le.trans hDegree
  have hVQNot : simpleEdge v D.q D.hvq ∉ P.edges := by
    rw [← D.vq_missing]
    exact P.missing_not_live t
  have hCollinear :
      PinCollinearity.Collinear
        (Yp.position v) (Yp.position D.p) (Yp.position D.q) := by
    apply pinCollinear_of_affinelyCollinearOn
      Yp.position (P.terminals t) v D.p D.q (Yp.collinear t)
    · rw [D.terminals]
      simp
    · rw [D.terminals]
      simp
    · rw [D.terminals]
      simp
  have hChildCard :
      Fintype.card (RemainingVertex v) < Fintype.card V := by
    have hDrop := card_remainingVertex_add_one v
    omega
  rcases private_nonexceptional_or_exceptional
      (k := k) P.edges Yp.position v with hPaid | hExceptionalPivot
  · have hChildSparse :=
      P.deletePrivate_completionSparse v t D.multiplicity
        D.mem_terminal D.completionSparse
    have hChild :
        (Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal).SemismallBudget
          (P.deletePrivate v t D.multiplicity D.mem_terminal) := by
      exact hSmaller hChildCard
        (P.deletePrivate v t D.multiplicity D.mem_terminal)
        (Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal)
        hChildSparse
    apply Y.semismallBudget_of_privatePivot S hSparse D
    exact Yp.semismallBudget_of_deletePrivateIntrinsic P v t
      D.multiplicity D.mem_terminal hChild hPaid
  · obtain ⟨_Nclass, _hqzClass, _hcolClass, hExtension,
      hResponse, _hLocalKernel, _hLocalRank, _hDegreeTwo,
      _hConnectingZero⟩ :=
      privateExceptional_classification (k := k)
        P.edges Yp.position v D.p D.q
        D.hvp D.hvq D.hpq D.vp_live hVQNot hDegreeP
        Yp.distinct hCollinear Yp.generated hExceptionalPivot
    obtain ⟨N, hqz, hpzRow, hqzRow⟩ :=
      privateExceptional_bothVirtualRows_mem (k := k)
        P.edges Yp.position v D.p D.q
        D.hvp D.hvq D.hpq D.vp_live D.pq_live hVQNot hDegreeP
        Yp.distinct hCollinear Yp.generated hExceptionalPivot
    obtain ⟨f, hfCases, hfCompletion, hAddable⟩ :=
      P.private_response_edge_addable D.completionSparse
        v D.p D.q N.z t D.hvp D.hvq N.hvz D.hpq N.hpz hqz
        D.terminals D.pq_live N.vz_mem
    have hvf : v ∉ f.vertices := by
      rcases hfCases with rfl | rfl
      · rw [vertices_simpleEdge]
        simp [D.hvp, N.hvz]
      · rw [vertices_simpleEdge]
        simp [D.hvq, N.hvz]
    have hfLive : f ∉ P.edges := by
      intro hf
      apply hfCompletion
      apply P.liftedLiveEdges_subset_completionEdges
      rw [P.mem_liftedLiveEdges]
      exact hf
    have hRow : directionRow Yp.position f ∈
        directionRowSpace (deleteVertexEdges P.edges v) Yp.position := by
      rcases hfCases with rfl | rfl
      · exact hpzRow
      · exact hqzRow
    obtain ⟨heMissing, hInsertedSparse⟩ :=
      P.exists_insertedPrivateChild_of_addable
        v t D.multiplicity D.mem_terminal f hvf hfCompletion hAddable
    let child := P.deletePrivate v t D.multiplicity D.mem_terminal
    let e := restrictSimpleEdge v f hvf
    let Z := Yp.deletePrivateIntrinsic P v t D.multiplicity D.mem_terminal
    let inserted := child.insertLiveEdge e heMissing
    let Zi := Z.insertLiveEdge child e heMissing
    have hInsertedBudget : Zi.SemismallBudget inserted := by
      exact hSmaller hChildCard inserted Zi hInsertedSparse
    apply Y.semismallBudget_of_privatePivot S hSparse D
    exact Yp.semismallBudget_of_insertedPrivateExceptional
      P v t D.multiplicity D.mem_terminal f hvf hfLive heMissing
      hExtension hResponse hRow hInsertedBudget

end ProvenanceFlag

end

end RB31E2E
