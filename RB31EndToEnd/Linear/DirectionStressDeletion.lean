import RB31EndToEnd.Linear.DirectionStress
import RB31EndToEnd.Linear.BlockKernelExact
import RB31EndToEnd.Combinatorics.Sparse22.Construction

/-!
# Exact direction-stress decomposition under deletion of one vertex

For a live edge set `F` and a vertex `v`, the edge weights split into old
weights on `deleteVertexEdges F v` and local weights on `incidentEdges F v`.
Vertex loads split into the rows away from `v` and the three-coordinate row
at `v`.  After these two literal linear equivalences, the parent direction
equilibrium map is the lower-triangular block map of `BlockKernelExact`.

Consequently the parent stress dimension is the deleted stress dimension
plus the dimension of the genuine connecting kernel.  No rank identity or
exactness assertion is supplied as a hypothesis.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The exact type of live vertices different from the deleted vertex. -/
abbrev AwayFrom (v : V) := {u : V // u ≠ v}

/-! ## Splitting edge weights -/

/-- The parent edge type is the disjoint sum of deleted and incident edge
types. -/
def edgeDeletionEquiv (F : SimpleEdgeSet V) (v : V) :
    F ≃ (↑(deleteVertexEdges F v) ⊕ ↑(incidentEdges F v)) where
  toFun e :=
    if hev : v ∈ e.1.vertices then
      Sum.inr ⟨e.1, mem_incidentEdges.mpr ⟨e.2, hev⟩⟩
    else
      Sum.inl ⟨e.1, mem_deleteVertexEdges.mpr ⟨e.2, hev⟩⟩
  invFun e := match e with
    | Sum.inl f => ⟨f.1, (mem_deleteVertexEdges.mp f.2).1⟩
    | Sum.inr f => ⟨f.1, (mem_incidentEdges.mp f.2).1⟩
  left_inv e := by
    by_cases hev : v ∈ e.1.vertices
    · simp [hev]
    · simp [hev]
  right_inv e := by
    cases e with
    | inl f =>
        have hev : v ∉ f.1.vertices := (mem_deleteVertexEdges.mp f.2).2
        simp [hev]
    | inr f =>
        have hev : v ∈ f.1.vertices := (mem_incidentEdges.mp f.2).2
        simp [hev]

/-- Restrict a parent weight to the deleted and incident edge packets, with
the inverse extending the two packets over their literal partition of `F`. -/
def splitEdgeWeights (F : SimpleEdgeSet V) (v : V) :
    (F → k) ≃ₗ[k]
      ((deleteVertexEdges F v → k) × (incidentEdges F v → k)) where
  toFun weight :=
    (fun e ↦ weight ⟨e.1, (mem_deleteVertexEdges.mp e.2).1⟩,
      fun e ↦ weight ⟨e.1, (mem_incidentEdges.mp e.2).1⟩)
  invFun weight e :=
    if hev : v ∈ e.1.vertices then
      weight.2 ⟨e.1, mem_incidentEdges.mpr ⟨e.2, hev⟩⟩
    else
      weight.1 ⟨e.1, mem_deleteVertexEdges.mpr ⟨e.2, hev⟩⟩
  left_inv weight := by
    funext e
    by_cases hev : v ∈ e.1.vertices
    · simp [hev]
    · simp [hev]
  right_inv weight := by
    apply Prod.ext
    · funext e
      have hev : v ∉ e.1.vertices := (mem_deleteVertexEdges.mp e.2).2
      simp [hev]
    · funext e
      have hev : v ∈ e.1.vertices := (mem_incidentEdges.mp e.2).2
      simp [hev]
  map_add' _x _y := by
    apply Prod.ext <;> funext e <;> rfl
  map_smul' _c _x := by
    apply Prod.ext <;> funext e <;> rfl

/-! ## Splitting vertex loads -/

/-- Restrict a vertex load to the vertices away from `v`. -/
def restrictAway (v : V) :
    (V → Fin 3 → k) →ₗ[k] (AwayFrom v → Fin 3 → k) where
  toFun load u := load u.1
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

/-- Evaluate a vertex load at the deleted vertex. -/
def loadAt (v : V) : (V → Fin 3 → k) →ₗ[k] (Fin 3 → k) where
  toFun load := load v
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

/-- A load on all vertices is equivalent to its away-from-`v` rows and its
row at `v`. -/
def splitVertexLoads (v : V) :
    (V → Fin 3 → k) ≃ₗ[k]
      ((AwayFrom v → Fin 3 → k) × (Fin 3 → k)) where
  toFun load := (fun u ↦ load u.1, load v)
  invFun load u := if huv : u = v then load.2 else load.1 ⟨u, huv⟩
  left_inv load := by
    funext u
    by_cases huv : u = v
    · subst u
      simp
    · simp [huv]
  right_inv load := by
    apply Prod.ext
    · funext u
      simp [u.2]
    · simp
  map_add' _x _y := by
    apply Prod.ext <;> rfl
  map_smul' _c _x := by
    apply Prod.ext <;> rfl

/-! ## The three deletion blocks -/

/-- Equilibrium of the deleted edge packet, restricted to old vertex rows. -/
def oldEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (deleteVertexEdges F v → k) →ₗ[k] (AwayFrom v → Fin 3 → k) :=
  (restrictAway v).comp (directionEquilibrium (deleteVertexEdges F v) a)

/-- Contribution of incident edge weights to old vertex rows. -/
def localToOldEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (incidentEdges F v → k) →ₗ[k] (AwayFrom v → Fin 3 → k) :=
  (restrictAway v).comp (directionEquilibrium (incidentEdges F v) a)

/-- Equilibrium at the deleted vertex contributed by incident edge weights. -/
def localEquilibriumAt
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    (incidentEdges F v → k) →ₗ[k] (Fin 3 → k) :=
  (loadAt v).comp (directionEquilibrium (incidentEdges F v) a)

/-- The parent equilibrium after the literal domain and codomain splits. -/
def splitDirectionEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    ((deleteVertexEdges F v → k) × (incidentEdges F v → k)) →ₗ[k]
      ((AwayFrom v → Fin 3 → k) × (Fin 3 → k)) :=
  (splitVertexLoads v).toLinearMap.comp
    ((directionEquilibrium F a).comp (splitEdgeWeights F v).symm.toLinearMap)

omit [Fintype V] in
private theorem directionRow_deleted_vertex_eq_zero
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (e : deleteVertexEdges F v) :
    directionRow a e.1 v = 0 := by
  have hev : v ∉ e.1.vertices := (mem_deleteVertexEdges.mp e.2).2
  have hsourceMem : e.1.source ∈ e.1.vertices := by
    simp [SimpleEdge.vertices, ← e.1.source_target_mk, Sym2.toFinset_mk_eq]
  have htargetMem : e.1.target ∈ e.1.vertices := by
    simp [SimpleEdge.vertices, ← e.1.source_target_mk, Sym2.toFinset_mk_eq]
  apply directionRow_eq_zero_of_ne
  · intro h
    rw [h] at hsourceMem
    exact hev hsourceMem
  · intro h
    rw [h] at htargetMem
    exact hev htargetMem

omit [Fintype V] in
/-- Deleted edges contribute zero load at the deleted vertex. -/
@[simp]
theorem old_packet_equilibrium_at_deleted
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V)
    (weight : deleteVertexEdges F v → k) :
    directionEquilibrium (deleteVertexEdges F v) a weight v = 0 := by
  funext j
  simp only [directionEquilibrium_apply, directionEquilibriumCoordinate]
  apply Finset.sum_eq_zero
  intro e _he
  rw [directionRow_deleted_vertex_eq_zero F a v e]
  simp

omit [Fintype V] in
private theorem directionEquilibriumCoordinate_split
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v u : V) (j : Fin 3)
    (weight :
      (deleteVertexEdges F v → k) × (incidentEdges F v → k)) :
    directionEquilibriumCoordinate F a
        ((splitEdgeWeights F v).symm weight) u j =
      directionEquilibriumCoordinate (deleteVertexEdges F v) a weight.1 u j +
        directionEquilibriumCoordinate (incidentEdges F v) a weight.2 u j := by
  let g : (deleteVertexEdges F v → k) × (incidentEdges F v → k) := weight
  let summand : F → k := fun e ↦
    ((splitEdgeWeights F v).symm weight) e * directionRow a e.1 u j
  let splitSummand :
      (deleteVertexEdges F v ⊕ incidentEdges F v) → k
    | Sum.inl e => weight.1 e * directionRow a e.1 u j
    | Sum.inr e => weight.2 e * directionRow a e.1 u j
  have hReindex : (∑ e : F, summand e) =
      ∑ e : (deleteVertexEdges F v ⊕ incidentEdges F v), splitSummand e := by
    exact Fintype.sum_equiv (edgeDeletionEquiv F v)
      summand splitSummand (fun e ↦ by
        by_cases hev : v ∈ e.1.vertices
        · simp [summand, splitSummand, edgeDeletionEquiv, splitEdgeWeights, hev]
        · simp [summand, splitSummand, edgeDeletionEquiv, splitEdgeWeights, hev])
  change (∑ e : F, summand e) =
    (∑ e : deleteVertexEdges F v,
      weight.1 e * directionRow a e.1 u j) +
    ∑ e : incidentEdges F v,
      weight.2 e * directionRow a e.1 u j
  rw [hReindex]
  exact Fintype.sum_sum_type splitSummand

omit [Fintype V] in
/-- The transformed parent map is exactly the `A/B/C` block map. -/
theorem splitDirectionEquilibrium_eq_blockMap
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    splitDirectionEquilibrium F a v =
      BlockKernelExact.blockMap
        (oldEquilibrium F a v)
        (localToOldEquilibrium F a v)
        (localEquilibriumAt F a v) := by
  apply LinearMap.ext
  intro weight
  apply Prod.ext
  · funext u j
    exact directionEquilibriumCoordinate_split F a v u.1 j weight
  · funext j
    have hsplit := directionEquilibriumCoordinate_split F a v v j weight
    have hOldZero := congrFun
      (old_packet_equilibrium_at_deleted F a v weight.1) j
    change directionEquilibriumCoordinate (deleteVertexEdges F v) a
      weight.1 v j = 0 at hOldZero
    rw [hOldZero, zero_add] at hsplit
    simpa [splitDirectionEquilibrium, oldEquilibrium, localToOldEquilibrium,
      localEquilibriumAt] using hsplit

/-! ## Kernel identifications and the dimension formula -/

/-- Splitting edge weights identifies the parent stress kernel with the
kernel of the literal block map. -/
def parentStressEquivBlockKernel
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    DirectionStressSpace F a ≃ₗ[k]
      LinearMap.ker
        (BlockKernelExact.blockMap
          (oldEquilibrium F a v)
          (localToOldEquilibrium F a v)
          (localEquilibriumAt F a v)) where
  toFun weight := by
    refine ⟨splitEdgeWeights F v weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    have hParent := LinearMap.mem_ker.mp weight.2
    have hSplit :
        splitDirectionEquilibrium F a v (splitEdgeWeights F v weight.1) = 0 := by
      change splitVertexLoads v
        (directionEquilibrium F a
          ((splitEdgeWeights F v).symm (splitEdgeWeights F v weight.1))) = 0
      rw [(splitEdgeWeights F v).symm_apply_apply, hParent]
      simp
    calc
      BlockKernelExact.blockMap
          (oldEquilibrium F a v)
          (localToOldEquilibrium F a v)
          (localEquilibriumAt F a v)
          (splitEdgeWeights F v weight.1) =
          splitDirectionEquilibrium F a v (splitEdgeWeights F v weight.1) := by
        exact (congrArg
          (fun L ↦ L (splitEdgeWeights F v weight.1))
          (splitDirectionEquilibrium_eq_blockMap F a v)).symm
      _ = 0 := hSplit
  invFun weight := by
    refine ⟨(splitEdgeWeights F v).symm weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    have hblock := LinearMap.mem_ker.mp weight.2
    have hSplit : splitDirectionEquilibrium F a v weight.1 = 0 := by
      calc
        splitDirectionEquilibrium F a v weight.1 =
            BlockKernelExact.blockMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v) weight.1 := by
          exact congrArg (fun L ↦ L weight.1)
            (splitDirectionEquilibrium_eq_blockMap F a v)
        _ = 0 := hblock
    change splitVertexLoads v
      (directionEquilibrium F a ((splitEdgeWeights F v).symm weight.1)) = 0 at hSplit
    apply (splitVertexLoads v).injective
    simpa using hSplit
  left_inv weight := by
    apply Subtype.ext
    exact (splitEdgeWeights F v).symm_apply_apply weight.1
  right_inv weight := by
    apply Subtype.ext
    exact (splitEdgeWeights F v).apply_symm_apply weight.1
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- Restricting deleted-edge equilibrium to away-from-`v` rows loses no
kernel information, because its row at `v` is identically zero. -/
def oldKernelEquivDeletedStress
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    LinearMap.ker (oldEquilibrium F a v) ≃ₗ[k]
      DirectionStressSpace (deleteVertexEdges F v) a where
  toFun weight := by
    refine ⟨weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    by_cases huv : u = v
    · subst u
      exact old_packet_equilibrium_at_deleted F a v weight.1
    · have hold := LinearMap.mem_ker.mp weight.2
      have hu := congrFun hold ⟨u, huv⟩
      change directionEquilibrium (deleteVertexEdges F v) a weight.1 u = 0 at hu
      exact hu
  invFun weight := by
    refine ⟨weight.1, ?_⟩
    rw [LinearMap.mem_ker]
    funext u
    have h := LinearMap.mem_ker.mp weight.2
    exact congrFun h u.1
  left_inv weight := by
    apply Subtype.ext
    rfl
  right_inv weight := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    rfl

/-- Exact deletion formula for direction stresses.  The second summand is
the kernel of the explicit local response in the old-row cokernel. -/
theorem directionStressDim_delete_add_connectingKernel
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (v : V) :
    directionStressDim F a =
      directionStressDim (deleteVertexEdges F v) a +
        Module.finrank k
          (LinearMap.ker
            (BlockKernelExact.connectingMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v))) := by
  calc
    directionStressDim F a =
        Module.finrank k
          (LinearMap.ker
            (BlockKernelExact.blockMap
              (oldEquilibrium F a v)
              (localToOldEquilibrium F a v)
              (localEquilibriumAt F a v))) := by
      exact (parentStressEquivBlockKernel F a v).finrank_eq
    _ = Module.finrank k (LinearMap.ker (oldEquilibrium F a v)) +
          Module.finrank k
            (LinearMap.ker
              (BlockKernelExact.connectingMap
                (oldEquilibrium F a v)
                (localToOldEquilibrium F a v)
                (localEquilibriumAt F a v))) := by
      exact BlockKernelExact.finrank_blockKernel
        (oldEquilibrium F a v)
        (localToOldEquilibrium F a v)
        (localEquilibriumAt F a v)
    _ = directionStressDim (deleteVertexEdges F v) a +
          Module.finrank k
            (LinearMap.ker
              (BlockKernelExact.connectingMap
                (oldEquilibrium F a v)
                (localToOldEquilibrium F a v)
                (localEquilibriumAt F a v))) := by
      rw [(oldKernelEquivDeletedStress F a v).finrank_eq]
      rfl

end

end DirectionStress

end RB31E2E
