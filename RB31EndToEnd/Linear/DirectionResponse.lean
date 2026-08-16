import RB31EndToEnd.Linear.DirectionStressDeletion

/-!
# Direction-row spaces and the minimal local response calculus

The response of a deleted vertex is not stored in a record.  It is the
literal class of the local away-load in the cokernel of the old equilibrium
map.  This file identifies vanishing of that class with membership in the
span of the child direction rows.

It also proves the common augmentation fact used by both outside and
private-flag reductions: adjoining an absent edge whose direction row is
already in the old row space leaves row rank unchanged and increases stress
dimension by exactly one.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-! ## Literal row spaces -/

/-- The span of the actual labelled direction rows of `F`. -/
def directionRowSpace (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    Submodule k (V → Fin 3 → k) :=
  Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1))

omit [Fintype V] in
/-- The literal row space is the range of equilibrium synthesis. -/
theorem directionRowSpace_eq_range
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionRowSpace F a = LinearMap.range (directionEquilibrium F a) := by
  exact (range_directionEquilibrium_eq_span_directionRows F a).symm

omit [Fintype V] in
/-- Row rank is the finite dimension of the literal row space. -/
theorem directionEquilibriumRank_eq_finrank_rowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a = Module.finrank k (directionRowSpace F a) := by
  rw [directionEquilibriumRank, ← directionRowSpace_eq_range]

/-- The child row space transported to the vertex rows away from `v`. -/
def deletedAwayRowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    Submodule k (AwayFrom v → Fin 3 → k) :=
  (directionRowSpace (deleteVertexEdges F v) a).map (restrictAway v)

omit [Fintype V] in
/-- The old block map has exactly the transported child row space as its
range. -/
theorem range_oldEquilibrium_eq_deletedAwayRowSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.range (oldEquilibrium F a v) = deletedAwayRowSpace F a v := by
  ext load
  constructor
  · rintro ⟨weight, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨directionEquilibrium (deleteVertexEdges F v) a weight, ?_, rfl⟩
    rw [directionRowSpace_eq_range]
    exact ⟨weight, rfl⟩
  · intro hload
    obtain ⟨childLoad, hChildLoad, rfl⟩ := Submodule.mem_map.mp hload
    rw [directionRowSpace_eq_range] at hChildLoad
    obtain ⟨weight, rfl⟩ := hChildLoad
    exact ⟨weight, rfl⟩

/-! ## The local response class -/

/-- The actual child-load class of a locally equilibrated incident weight.
Its codomain is the old-row cokernel; this is precisely the connecting map
from the deletion exact sequence. -/
def deletedConnectingClass
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.ker (localEquilibriumAt F a v) →ₗ[k]
      ((AwayFrom v → Fin 3 → k) ⧸
        LinearMap.range (oldEquilibrium F a v)) :=
  BlockKernelExact.connectingMap
    (oldEquilibrium F a v)
    (localToOldEquilibrium F a v)
    (localEquilibriumAt F a v)

omit [Fintype V] in
@[simp]
theorem deletedConnectingClass_apply
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    deletedConnectingClass F a v z =
      (LinearMap.range (oldEquilibrium F a v)).mkQ
        (localToOldEquilibrium F a v z.1) :=
  rfl

omit [Fintype V] in
/-- Vanishing of the response class is exactly provenance-preserving
descent of the local away-load into the transported child row space. -/
theorem deletedConnectingClass_eq_zero_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    deletedConnectingClass F a v z = 0 ↔
      localToOldEquilibrium F a v z.1 ∈ deletedAwayRowSpace F a v := by
  rw [deletedConnectingClass_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero,
    ← range_oldEquilibrium_eq_deletedAwayRowSpace]

omit [Fintype V] in
/-- Kernel membership form of the same response criterion. -/
theorem mem_ker_deletedConnectingClass_iff
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (z : LinearMap.ker (localEquilibriumAt F a v)) :
    z ∈ LinearMap.ker (deletedConnectingClass F a v) ↔
      localToOldEquilibrium F a v z.1 ∈ deletedAwayRowSpace F a v := by
  rw [LinearMap.mem_ker, deletedConnectingClass_eq_zero_iff]

/-! ## Adjoining a virtual response edge -/

omit [Fintype V] in
/-- Old direction rows remain in the row space after adjoining any edge. -/
theorem directionRowSpace_le_insert
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V) :
    directionRowSpace F a ≤ directionRowSpace (insert f F) a := by
  rw [directionRowSpace, directionRowSpace, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨e.1, Finset.mem_insert_of_mem e.2⟩, rfl⟩

omit [Fintype V] in
/-- If the adjoined row already belongs to the old row space, no new row
direction is created. -/
theorem directionRowSpace_insert_le_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionRowSpace (insert f F) a ≤ directionRowSpace F a := by
  rw [directionRowSpace, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  by_cases hef : e.1 = f
  · simpa [hef] using hrow
  · apply Submodule.subset_span
    refine ⟨⟨e.1, ?_⟩, rfl⟩
    exact (Finset.mem_insert.mp e.2).resolve_left hef

omit [Fintype V] in
/-- Exact row-space invariance under adjoining a virtual response row. -/
theorem directionRowSpace_insert_eq_of_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionRowSpace (insert f F) a = directionRowSpace F a := by
  apply le_antisymm
  · exact directionRowSpace_insert_le_of_mem F a f hrow
  · exact directionRowSpace_le_insert F a f

/-- Reusable augmentation theorem: an absent edge whose direction row is a
child response increases stress dimension by exactly one. -/
theorem directionStressDim_insert_eq_add_one_of_row_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hf : f ∉ F) (hrow : directionRow a f ∈ directionRowSpace F a) :
    directionStressDim (insert f F) a = directionStressDim F a + 1 := by
  have hRank : directionEquilibriumRank (insert f F) a =
      directionEquilibriumRank F a := by
    rw [directionEquilibriumRank_eq_finrank_rowSpace,
      directionEquilibriumRank_eq_finrank_rowSpace,
      directionRowSpace_insert_eq_of_mem F a f hrow]
  have hParent := directionStressDim_add_directionEquilibriumRank
    (insert f F) a
  have hChild := directionStressDim_add_directionEquilibriumRank F a
  rw [Finset.card_insert_of_notMem hf, hRank] at hParent
  omega

/-- The same theorem phrased directly as the common virtual-response
certificate used by deletion branches. -/
theorem stress_augmentation_of_virtual_response
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (f : SimpleEdge V)
    (hf : f ∉ F)
    (hVirtualResponse : directionRow a f ∈ directionRowSpace F a) :
    directionStressDim (insert f F) a = directionStressDim F a + 1 :=
  directionStressDim_insert_eq_add_one_of_row_mem F a f hf hVirtualResponse

end

end DirectionStress

end RB31E2E
