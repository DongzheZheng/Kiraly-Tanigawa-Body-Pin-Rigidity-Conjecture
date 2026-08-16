import RB31EndToEnd.NullCellule.ProvenanceFlagPlacement
import RB31EndToEnd.Linear.DirectionStressVertexDeletion
import RB31EndToEnd.Linear.DirectionStressBaseChange

/-!
# Exact budget transport across provenance-flag deletion

This file is the numerical interface consumed by the strong induction.
It constructs the actual outside and private child placements on their
literal subtype states, identifies their stress dimensions with the parent
deleted graph, and proves the two local budget lifts:

* outside deletion consumes at most three coordinates;
* private deletion consumes one coordinate but also removes one flag, so
  the local allowance is exactly one.

All branch dimensions are the transcendence degrees of actual coordinate
fields, and the tower equality is `CoordinateFieldTower.trdeg_add_eq`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Literal child placements -/

/-- Restrict an ambient-field placement branch to an outside-deletion
child. -/
def PlacementBranch.deleteOutsidePlacement
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    PlacementBranch (K := K) (S.deleteOutside v hv) where
  position := restrictPlacement Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    exact Y.distinct hab
  collinear t := by
    obtain ⟨origin, direction, hall⟩ := Y.collinear t
    refine ⟨origin, direction, ?_⟩
    intro a ha
    exact hall a.1
      ((mem_restrictVertexSet_iff v (S.terminals t)
        (not_mem_terminals_of_flagMultiplicity_eq_zero S v hv t) a).1 ha)

/-- Restrict an ambient-field placement branch to a private-deletion child,
simultaneously consuming its unique flag. -/
def PlacementBranch.deletePrivatePlacement
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    PlacementBranch (K := K) (S.deletePrivate v t hOne hvt) where
  position := restrictPlacement Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    exact Y.distinct hab
  collinear r := by
    obtain ⟨origin, direction, hall⟩ := Y.collinear r.1
    refine ⟨origin, direction, ?_⟩
    intro a ha
    exact hall a.1
      ((mem_restrictVertexSet_iff v (S.terminals r.1)
        (not_mem_other_terminals_of_flagMultiplicity_eq_one
          S v t hOne hvt r.1 r.2) a).1 ha)

@[simp]
theorem deleteOutsidePlacement_position
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    (Y.deleteOutsidePlacement S v hv).position =
      restrictPlacement Y.position v := rfl

@[simp]
theorem deletePrivatePlacement_position
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (Y.deletePrivatePlacement S v t hOne hvt).position =
      restrictPlacement Y.position v := rfl

/-! ## Cross-type stress and coordinate-field identities -/

/-- The outside child stress is exactly the stress of the parent's
vertex-deleted edge set. -/
theorem PlacementBranch.deleteOutsidePlacement_stressDim
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    (Y.deleteOutsidePlacement S v hv).stressDim (S.deleteOutside v hv) =
      directionStressDim (deleteVertexEdges S.edges v) Y.position := by
  exact directionStressDim_restrictedLiveEdges S.edges Y.position v

/-- The same exact stress identity for the private child. -/
theorem PlacementBranch.deletePrivatePlacement_stressDim
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    (Y.deletePrivatePlacement S v t hOne hvt).stressDim
        (S.deletePrivate v t hOne hvt) =
      directionStressDim (deleteVertexEdges S.edges v) Y.position := by
  exact directionStressDim_restrictedLiveEdges S.edges Y.position v

omit [Fintype V] [DecidableEq V] in
/-- The child's intrinsic coordinate field is definitionally the retained
coordinate field used by the deletion ledger. -/
theorem liveCoordinateField_restrictPlacement
    (a : V → Fin 3 → K) (v : V) :
    liveCoordinateField (k := k) (restrictPlacement a v) =
      retainedCoordinateField (k := k) a v := by
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Exact transcendence-degree tower from the child coordinate field to a
coordinate-generated parent function field. -/
theorem trdeg_child_add_outsideExtension
    (a : V → Fin 3 → K) (v : V)
    (_hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤) :
    Algebra.trdeg k
        (liveCoordinateField (k := k) (restrictPlacement a v)) +
      outsideExtensionTrdeg (k := k) a v =
        Algebra.trdeg k K := by
  rw [liveCoordinateField_restrictPlacement]
  exact CoordinateFieldTower.trdeg_old_add_extension
    (k := k) (retainedCoordinates a v)

/-! ## Finite cardinal ledgers -/

theorem card_remainingVertex_add_one (v : V) :
    Fintype.card (RemainingVertex v) + 1 = Fintype.card V := by
  have hcard : Fintype.card (RemainingVertex v) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun u : V ↦ u = v)]
    simp
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

theorem card_remainingFlag_add_one (t : Flag) :
    Fintype.card (RemainingFlag t) + 1 = Fintype.card Flag := by
  have hcard : Fintype.card (RemainingFlag t) = Fintype.card Flag - 1 := by
    rw [Fintype.card_subtype_compl (fun u : Flag ↦ u = t)]
    simp
  have hpos : 0 < Fintype.card Flag := Fintype.card_pos_iff.mpr ⟨t⟩
  omega

/-! ## The intrinsic child coordinate field -/

/-- The exact field generated by all coordinates retained after deleting
`v`. -/
abbrev retainedLiveCoordinateField
    (a : V → Fin 3 → K) (v : V) : IntermediateField k K :=
  liveCoordinateField (k := k) (restrictPlacement a v)

/-- The retained placement, now genuinely valued in its own intrinsic
coordinate field. -/
def intrinsicRestrictedPlacement
    (a : V → Fin 3 → K) (v : V) :
    RemainingVertex v → Fin 3 → retainedLiveCoordinateField (k := k) a v :=
  fun u j ↦
    ⟨a u.1 j, IntermediateField.subset_adjoin k
      (Set.range (liveCoordinateFamily (restrictPlacement a v)))
      ⟨(u, j), rfl⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- Scalar-extending the intrinsic child placement recovers the ambient
restricted placement coordinatewise. -/
theorem map_intrinsicRestrictedPlacement
    (a : V → Fin 3 → K) (v : V) :
    mapPlacement (K := K) (intrinsicRestrictedPlacement (k := k) a v) =
      restrictPlacement a v := by
  funext u j
  rfl

omit [Fintype V] [DecidableEq V] in
/-- The intrinsic retained coordinates generate their field by
construction. -/
theorem intrinsicRestrictedPlacement_generated
    (a : V → Fin 3 → K) (v : V) :
    IntermediateField.adjoin k
      (Set.range (liveCoordinateFamily
        (intrinsicRestrictedPlacement (k := k) a v))) = ⊤ := by
  let L := retainedLiveCoordinateField (k := k) a v
  let x : RemainingVertex v × Fin 3 → L := fun c ↦
    intrinsicRestrictedPlacement (k := k) a v c.1 c.2
  apply top_unique
  intro y _hy
  exact IntermediateField.adjoin_induction k
    (p := fun z hz ↦
      (⟨z, hz⟩ : L) ∈ IntermediateField.adjoin k (Set.range x))
    (fun z hz ↦ by
      obtain ⟨c, rfl⟩ := hz
      exact IntermediateField.subset_adjoin k (Set.range x) ⟨c, rfl⟩)
    (fun z ↦ (IntermediateField.adjoin k (Set.range x)).algebraMap_mem z)
    (fun _ _ _ _ hz hw ↦
      (IntermediateField.adjoin k (Set.range x)).add_mem hz hw)
    (fun _ _ hz ↦
      (IntermediateField.adjoin k (Set.range x)).inv_mem hz)
    (fun _ _ _ _ hz hw ↦
      (IntermediateField.adjoin k (Set.range x)).mul_mem hz hw)
    y.property

/-- Base change plus literal vertex reindexing identifies the child stress
computed over its intrinsic field with the parent deleted stress. -/
theorem directionStressDim_intrinsicRestrictedPlacement
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    directionStressDim (restrictedLiveEdges F v)
        (intrinsicRestrictedPlacement (k := k) a v) =
      directionStressDim (deleteVertexEdges F v) a := by
  calc
    directionStressDim (restrictedLiveEdges F v)
        (intrinsicRestrictedPlacement (k := k) a v) =
      directionStressDim (restrictedLiveEdges F v)
        (mapPlacement (K := K)
          (intrinsicRestrictedPlacement (k := k) a v)) :=
        (directionStressDim_mapPlacement
          (K := K) (restrictedLiveEdges F v)
          (intrinsicRestrictedPlacement (k := k) a v)).symm
    _ = directionStressDim (restrictedLiveEdges F v)
        (restrictPlacement a v) := by
      rw [map_intrinsicRestrictedPlacement]
    _ = directionStressDim (deleteVertexEdges F v) a :=
      directionStressDim_restrictedLiveEdges F a v

/-- Outside-child semismallness is equivalently computed using the stress
matrix over the child's intrinsic coordinate field. -/
theorem PlacementBranch.deleteOutside_semismallBudget_iff_intrinsic
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0) :
    PlacementBranch.SemismallBudget (k := k)
        (S.deleteOutside v hv) (Y.deleteOutsidePlacement S v hv) ↔
      (directionStressDim (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) := by
  unfold PlacementBranch.SemismallBudget PlacementBranch.stressDim
  change
    (directionStressDim (restrictedLiveEdges S.edges v)
          (restrictPlacement Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) ↔ _
  rw [← directionStressDim_mapPlacement
    (K := K) (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v),
    map_intrinsicRestrictedPlacement]

/-- Private-child semismallness has the same intrinsic-field
interpretation, with the consumed flag removed from the cardinal term. -/
theorem PlacementBranch.deletePrivate_semismallBudget_iff_intrinsic
    (S : State V Flag) (Y : PlacementBranch (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    PlacementBranch.SemismallBudget (k := k)
        (S.deletePrivate v t hOne hvt)
        (Y.deletePrivatePlacement S v t hOne hvt) ↔
      (directionStressDim (restrictedLiveEdges S.edges v)
          (intrinsicRestrictedPlacement (k := k) Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card (RemainingFlag t) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) := by
  unfold PlacementBranch.SemismallBudget PlacementBranch.stressDim
  change
    (directionStressDim (restrictedLiveEdges S.edges v)
          (restrictPlacement Y.position v) : Cardinal) +
          Algebra.trdeg k
            (retainedLiveCoordinateField (k := k) Y.position v) +
          2 * (Fintype.card (RemainingFlag t) : Cardinal) ≤
        3 * (Fintype.card (RemainingVertex v) : Cardinal) ↔ _
  rw [← directionStressDim_mapPlacement
    (K := K) (restrictedLiveEdges S.edges v)
    (intrinsicRestrictedPlacement (k := k) Y.position v),
    map_intrinsicRestrictedPlacement]

/-! ## The two direct induction interfaces -/

/-- **Outside nonexceptional budget lift.**  A semismall outside child and
the literal local payment `u + d ≤ 3` imply the parent flag budget. -/
theorem FunctionFieldBranch.semismallBudget_of_deleteOutside
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (hv : S.flagMultiplicity v = 0)
    (hChild : PlacementBranch.SemismallBudget (k := k)
      (S.deleteOutside v hv)
      ((Y.toPlacement S).deleteOutsidePlacement S v hv))
    (hLocal :
      (outsideResponseKernelDim S.edges Y.position v : Cardinal) +
        outsideExtensionTrdeg (k := k) Y.position v ≤ 3) :
    Y.SemismallBudget S := by
  let child := (Y.toPlacement S).deleteOutsidePlacement S v hv
  have hStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim (deleteVertexEdges S.edges v) Y.position : Cardinal) +
          (outsideResponseKernelDim S.edges Y.position v : Cardinal) := by
    exact_mod_cast hStress
  have hChildStress :=
    (Y.toPlacement S).deleteOutsidePlacement_stressDim S v hv
  have hChildStress' :
      child.stressDim (S.deleteOutside v hv) =
        directionStressDim (deleteVertexEdges S.edges v) Y.position := by
    simpa [child] using hChildStress
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hTower' :
      Algebra.trdeg k (liveCoordinateField (k := k) child.position) +
          outsideExtensionTrdeg (k := k) Y.position v =
        Algebra.trdeg k K := by
    simpa [child] using hTower
  have hVCard := card_remainingVertex_add_one v
  unfold PlacementBranch.SemismallBudget at hChild
  unfold FunctionFieldBranch.SemismallBudget
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((child.stressDim (S.deleteOutside v hv) : Cardinal) +
            Algebra.trdeg k
              (liveCoordinateField (k := k) child.position) +
            2 * (Fintype.card Flag : Cardinal)) +
          ((outsideResponseKernelDim S.edges Y.position v : Cardinal) +
            outsideExtensionTrdeg (k := k) Y.position v) := by
      rw [hStressC, ← hChildStress', ← hTower']
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 3 :=
      add_le_add hChild hLocal
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 3 = 3 * Fintype.card V)

/-- **Private nonexceptional budget lift.**  Removing one live vertex and
one flag changes the ambient ledger by `3 - 2 = 1`; hence the transparent
local payment `u + d ≤ 1` is exactly sufficient. -/
theorem FunctionFieldBranch.semismallBudget_of_deletePrivate
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hChild : PlacementBranch.SemismallBudget (k := k)
      (S.deletePrivate v t hOne hvt)
      ((Y.toPlacement S).deletePrivatePlacement S v t hOne hvt))
    (hLocal :
      (outsideResponseKernelDim S.edges Y.position v : Cardinal) +
        outsideExtensionTrdeg (k := k) Y.position v ≤ 1) :
    Y.SemismallBudget S := by
  let child :=
    (Y.toPlacement S).deletePrivatePlacement S v t hOne hvt
  have hStress := directionStressDim_eq_delete_add_outsideResponseKernelDim
    S.edges Y.position v
  have hStressC :
      (directionStressDim S.edges Y.position : Cardinal) =
        (directionStressDim (deleteVertexEdges S.edges v) Y.position : Cardinal) +
          (outsideResponseKernelDim S.edges Y.position v : Cardinal) := by
    exact_mod_cast hStress
  have hChildStress :=
    (Y.toPlacement S).deletePrivatePlacement_stressDim
      S v t hOne hvt
  have hChildStress' :
      child.stressDim (S.deletePrivate v t hOne hvt) =
        directionStressDim (deleteVertexEdges S.edges v) Y.position := by
    simpa [child] using hChildStress
  have hTower := trdeg_child_add_outsideExtension
    (k := k) Y.position v Y.generated
  have hTower' :
      Algebra.trdeg k (liveCoordinateField (k := k) child.position) +
          outsideExtensionTrdeg (k := k) Y.position v =
        Algebra.trdeg k K := by
    simpa [child] using hTower
  have hVCard := card_remainingVertex_add_one v
  have hFCard := card_remainingFlag_add_one t
  have hFCardC :
      (Fintype.card (RemainingFlag t) : Cardinal) + 1 =
        (Fintype.card Flag : Cardinal) := by
    exact_mod_cast hFCard
  unfold PlacementBranch.SemismallBudget at hChild
  unfold FunctionFieldBranch.SemismallBudget
  change
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) ≤
        3 * (Fintype.card V : Cardinal)
  calc
    (directionStressDim S.edges Y.position : Cardinal) +
          Algebra.trdeg k K + 2 * (Fintype.card Flag : Cardinal) =
        ((child.stressDim (S.deletePrivate v t hOne hvt) : Cardinal) +
            Algebra.trdeg k
              (liveCoordinateField (k := k) child.position) +
            2 * (Fintype.card (RemainingFlag t) : Cardinal)) +
          ((outsideResponseKernelDim S.edges Y.position v : Cardinal) +
            outsideExtensionTrdeg (k := k) Y.position v) + 2 := by
      rw [hStressC, ← hChildStress', ← hTower', ← hFCardC]
      ring
    _ ≤ 3 * (Fintype.card (RemainingVertex v) : Cardinal) + 1 + 2 :=
      add_le_add (add_le_add hChild hLocal) (le_refl 2)
    _ = 3 * (Fintype.card V : Cardinal) := by
      exact_mod_cast (by omega :
        3 * Fintype.card (RemainingVertex v) + 1 + 2 =
          3 * Fintype.card V)

end ProvenanceFlag

end

end RB31E2E
