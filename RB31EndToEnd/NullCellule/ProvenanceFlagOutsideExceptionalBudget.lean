import RB31EndToEnd.NullCellule.ProvenanceFlagOutsideRegisteredBranch
import RB31EndToEnd.NullCellule.ProvenanceFlagInsertedBranch
import RB31EndToEnd.Linear.OutsideExceptionalFullResponse
import RB31EndToEnd.Linear.DirectionResponseVertexDeletion
import RB31EndToEnd.Linear.OutsideRegistrationStress

/-!
# The exceptional outside budget

This file closes both outcomes of the exceptional outside degree-three
move.  In the incomplete outcome, a virtual neighbour row is inserted in
the literal outside child and recursive semismallness is transported back
with no numerical loss.  In the complete outcome, one collinear triangle
row is erased and the neighbour triple is registered as a new flag; stress
and flag codimension change by exactly two.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The edge returned by the triangle alternative is absent from the live
graph, since every lifted live edge belongs to the completion. -/
theorem outside_addable_edge_not_live
    (S : State V Flag) (f : SimpleEdge V)
    (hf : liftLiveEdge (Flag := Flag) f ∉ S.completionEdges) :
    f ∉ S.edges := by
  intro hfLive
  exact hf (S.liftedLiveEdges_subset_completionEdges
    ((S.mem_liftedLiveEdges f).2 hfLive))

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- Mapping the literal child edge joining two retained vertices recovers
the corresponding parent simple edge. -/
theorem mapSimpleEdge_remaining_simpleEdge
    (v p q : V) (hpv : p ≠ v) (hqv : q ≠ v) (hpq : p ≠ q) :
    Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
        (simpleEdge (⟨p, hpv⟩ : RemainingVertex v) ⟨q, hqv⟩
          (by intro h; exact hpq (congrArg Subtype.val h))) =
      simpleEdge p q hpq := by
  apply Subtype.ext
  simp only [Sparse22Transport.mapSimpleEdge_val, simpleEdge, Sym2.map_mk]
  rfl

/-- Inserting an exceptional virtual response into the intrinsic outside
child produces exactly the parent's stress dimension. -/
theorem outside_insertedChild_stress_eq_parent
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (hf : f ∉ deleteVertexEdges S.edges v)
    (hrow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1) :
    directionStressDim
        (insert (restrictSimpleEdge v f hvf)
          (S.deleteOutside v hv).edges)
        (intrinsicRestrictedPlacement (k := k) Y.position v) =
      Y.stressDim S := by
  have hIntrinsic := directionRow_intrinsicRestricted_mem_of_deleted_mem
    (L := k) S.edges Y.position v f hvf hf hrow
  have hfChild : restrictSimpleEdge v f hvf ∉
      (S.deleteOutside v hv).edges := by
    change restrictSimpleEdge v f hvf ∉ restrictedLiveEdges S.edges v
    intro hmem
    rw [mem_restrictedLiveEdges_iff, map_restrictSimpleEdge] at hmem
    exact hf hmem
  change directionStressDim
      (insert (restrictSimpleEdge v f hvf)
        (restrictedLiveEdges S.edges v))
      (intrinsicRestrictedPlacement (k := k) Y.position v) =
    Y.stressDim S
  rw [directionStressDim_insert_eq_add_one_of_row_mem
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    (restrictSimpleEdge v f hvf) hfChild hIntrinsic]
  have hIntrinsicStress := directionStressDim_intrinsicRestrictedPlacement
    (k := k) S.edges Y.position v
  rw [hIntrinsicStress]
  unfold FunctionFieldBranch.stressDim
  have hParentStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  rw [hParentStress, hResponse]

/-- A recursive budget for the inserted outside child implies the parent
budget in the exceptional `d=3, u=1` branch. -/
theorem FunctionFieldBranch.semismallBudget_of_outsideInsertedIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (f : SimpleEdge V) (hvf : v ∉ f.vertices)
    (heMissing : ∀ t : Flag,
      restrictSimpleEdge v f hvf ≠ (S.deleteOutside v hv).missing t)
    (hf : f ∉ deleteVertexEdges S.edges v)
    (hrow : directionRow Y.position f ∈
      directionRowSpace (deleteVertexEdges S.edges v) Y.position)
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hTrdeg : outsideExtensionTrdeg (k := k) Y.position v = 3)
    (hChild :
      ((Y.deleteOutsideIntrinsic S v hv).insertLiveEdge
        (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing).SemismallBudget
        ((S.deleteOutside v hv).insertLiveEdge
          (restrictSimpleEdge v f hvf) heMissing)) :
    Y.SemismallBudget S := by
  let L := retainedLiveCoordinateField (k := k) Y.position v
  let childState := (S.deleteOutside v hv).insertLiveEdge
    (restrictSimpleEdge v f hvf) heMissing
  let childBranch := (Y.deleteOutsideIntrinsic S v hv).insertLiveEdge
    (S.deleteOutside v hv) (restrictSimpleEdge v f hvf) heMissing
  have hStress := outside_insertedChild_stress_eq_parent
    (k := k) S Y v hv f hvf hf hrow hResponse
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hVCard := card_remainingVertex_add_one v
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  change
    (directionStressDim (insert (restrictSimpleEdge v f hvf)
        (S.deleteOutside v hv).edges)
        (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) at hChild
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        directionStressDim (insert (restrictSimpleEdge v f hvf)
          (S.deleteOutside v hv).edges)
          (intrinsicRestrictedPlacement (k := k) Y.position v) := by
    exact_mod_cast hStress.symm
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((directionStressDim (insert (restrictSimpleEdge v f hvf)
            (S.deleteOutside v hv).edges)
            (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card Flag : Cardinal)) + 3 := by
      rw [hStressC, ← hTower, hTrdeg]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      by simpa [add_comm] using add_le_add_left hChild 3
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

/-- In the complete branch, the registered child stress is exactly two
less than the parent stress. -/
theorem outside_registeredChild_stress_add_two_eq_parent
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r))
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1) :
    directionStressDim
        (S.registerOutside hSparse v hv N hTriangleLive).edges
        (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 =
      Y.stressDim S := by
  let e : SimpleEdge (RemainingVertex v) :=
    restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
      (not_mem_degreeThreeNeighbourPair N _ (by simp))
  have hChildCol : PinCollinearity.Collinear
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.p, N.hvp.symm⟩)
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.q, N.hvq.symm⟩)
      ((intrinsicRestrictedPlacement (k := k) Y.position v) ⟨N.r, N.hvr.symm⟩) := by
    apply collinear_restrictScalars
      (k := k) (K := K)
      (retainedLiveCoordinateField (k := k) Y.position v)
      _ _ _
    · intro hpq
      exact N.hpq (Y.distinct (by
        funext j
        exact congrArg Subtype.val (congrFun hpq j)))
    · simpa [intrinsicRestrictedPlacement] using hcol
  have hpqMemChild : simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.q, N.hvq.symm⟩ (by
        intro h; exact N.hpq (congrArg Subtype.val h)) ∈
      restrictedLiveEdges S.edges v := by
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.1,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hprMemChild : simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.r, N.hvr.symm⟩ (by
        intro h; exact N.hpr (congrArg Subtype.val h)) ∈
      (S.deleteOutside v hv).edges := by
    change simpleEdge
        (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
        ⟨N.r, N.hvr.symm⟩ _ ∈ restrictedLiveEdges S.edges v
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.2.1,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hqrMemChild : simpleEdge
      (⟨N.q, N.hvq.symm⟩ : RemainingVertex v)
      ⟨N.r, N.hvr.symm⟩ (by
        intro h; exact N.hqr (congrArg Subtype.val h)) ∈
      (S.deleteOutside v hv).edges := by
    change simpleEdge
        (⟨N.q, N.hvq.symm⟩ : RemainingVertex v)
        ⟨N.r, N.hvr.symm⟩ _ ∈ restrictedLiveEdges S.edges v
    rw [mem_restrictedLiveEdges_iff]
    rw [mapSimpleEdge_remaining_simpleEdge]
    exact mem_deleteVertexEdges.mpr
      ⟨hTriangleLive.2.2,
        not_mem_degreeThreeNeighbourPair N _ (by simp)⟩
  have hErase := directionStressDim_eq_erase_triangle_add_one
    (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v)
    (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
    ⟨N.q, N.hvq.symm⟩ ⟨N.r, N.hvr.symm⟩
    (by intro h; exact N.hpq (congrArg Subtype.val h))
    (by intro h; exact N.hpr (congrArg Subtype.val h))
    (by intro h; exact N.hqr (congrArg Subtype.val h))
    hpqMemChild hprMemChild hqrMemChild
    (by
      intro a b hab
      apply Subtype.ext
      apply Y.distinct
      funext j
      exact congrArg Subtype.val (congrFun hab j)) hChildCol
  have hParentDelete := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hIntrinsic := directionStressDim_intrinsicRestrictedPlacement
    (k := k) S.edges Y.position v
  have he : e = simpleEdge
      (⟨N.p, N.hvp.symm⟩ : RemainingVertex v)
      ⟨N.q, N.hvq.symm⟩ (by
        intro h; exact N.hpq (congrArg Subtype.val h)) := by
    apply Sparse22Transport.mapSimpleEdge_injective
      (remainingVertexEmbedding v)
    dsimp only [e]
    rw [map_restrictSimpleEdge, mapSimpleEdge_remaining_simpleEdge]
  change directionStressDim
      ((S.deleteOutside v hv).edges.erase e)
      (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 = _
  change directionStressDim
      ((restrictedLiveEdges S.edges v).erase e)
      (intrinsicRestrictedPlacement (k := k) Y.position v) + 2 = _
  rw [he]
  unfold FunctionFieldBranch.stressDim
  rw [hIntrinsic] at hErase
  rw [hParentDelete, hResponse, hErase]

/-- A recursive budget on the genuinely registered intrinsic branch pays
the exceptional complete outside move exactly. -/
theorem FunctionFieldBranch.semismallBudget_of_registerOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r))
    (hResponse : outsideResponseKernelDim S.edges Y.position v = 1)
    (hTrdeg : outsideExtensionTrdeg (k := k) Y.position v = 3)
    (hChild :
      (Y.registerOutsideIntrinsic S hSparse v hv N hTriangleLive hcol).SemismallBudget
      (S.registerOutside hSparse v hv N hTriangleLive)) :
    Y.SemismallBudget S := by
  let L := retainedLiveCoordinateField (k := k) Y.position v
  let registered := S.registerOutside hSparse v hv N hTriangleLive
  have hStress := outside_registeredChild_stress_add_two_eq_parent
    (k := k) S Y hSparse v hv N hTriangleLive hcol hResponse
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hVCard := card_remainingVertex_add_one v
  have hFlagCard : Fintype.card (Flag ⊕ Unit) = Fintype.card Flag + 1 := by
    simp
  unfold FunctionFieldBranch.SemismallBudget at hChild ⊢
  change
    (directionStressDim registered.edges
        (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card (Flag ⊕ Unit) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) at hChild
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim registered.edges
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) + 2 := by
    exact_mod_cast hStress.symm
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((directionStressDim registered.edges
            (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k L + 2 * (Fintype.card (Flag ⊕ Unit) : Cardinal)) + 3 := by
      rw [hStressC, ← hTower, hTrdeg, hFlagCard]
      push_cast
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      by simpa [add_comm] using add_le_add_left hChild 3
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

end ProvenanceFlag

end

end RB31E2E
