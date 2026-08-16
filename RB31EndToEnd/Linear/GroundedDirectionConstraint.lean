import RB31EndToEnd.Linear.FiniteRowSystem
import RB31EndToEnd.Linear.DirectionStress
import RB31EndToEnd.Algebra.GroundedTwist

/-!
# Grounded direction constraints

The translational projection of a grounded Split--Klein null system leaves
a linear system in the angular coordinates.  This file identifies that
system with the ordinary direction matrix and proves that deleting the root
load block does not change its stress space: every direction row has total
vertex load zero.
-/

namespace RB31E2E

namespace GroundedDirectionConstraint

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The three coordinate labels at all non-root vertices. -/
abbrev GroundedSpatialCoordinate (root : V) := OffRoot root × Fin 3

/-- One ordinary direction row restricted to non-root vertex blocks. -/
def groundedDirectionRow (root : V) (a : V → Fin 3 → k)
    (e : SimpleEdge V) : GroundedSpatialCoordinate root → k :=
  fun x ↦ DirectionStress.directionRow a e x.1.1 x.2

/-- The grounded direction constraint map. -/
def constraint (root : V) (F : SimpleEdgeSet V)
    (a : V → Fin 3 → k) :
    (GroundedSpatialCoordinate root → k) →ₗ[k] (F → k) :=
  FiniteRowSystem.constraint
    (fun e : F ↦ groundedDirectionRow root a e.1)

/-- Transpose synthesis using only non-root output blocks. -/
def synthesis (root : V) (F : SimpleEdgeSet V)
    (a : V → Fin 3 → k) :
    (F → k) →ₗ[k] (GroundedSpatialCoordinate root → k) :=
  FiniteRowSystem.synthesis
    (fun e : F ↦ groundedDirectionRow root a e.1)

omit [Fintype V] in
theorem synthesis_apply
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k) (x : GroundedSpatialCoordinate root) :
    synthesis root F a w x =
      DirectionStress.directionEquilibrium F a w x.1.1 x.2 := by
  simp [synthesis, FiniteRowSystem.synthesis, FiniteRowSystem.matrix,
    Matrix.vecMul, dotProduct,
    groundedDirectionRow, DirectionStress.directionEquilibrium_apply,
    DirectionStress.directionEquilibriumCoordinate]

/-- Every direction row has total vertex load zero in each spatial
coordinate. -/
theorem sum_directionRow_eq_zero
    (a : V → Fin 3 → k) (e : SimpleEdge V) (j : Fin 3) :
    ∑ v : V, DirectionStress.directionRow a e v j = 0 := by
  rw [show (∑ v : V, DirectionStress.directionRow a e v j) =
      (∑ v : V, if e.source = v then
          DirectionStress.edgeDirection a e j else 0) +
        (∑ v : V, if e.target = v then
          -DirectionStress.edgeDirection a e j else 0) by
    simp only [DirectionStress.directionRow, Finset.sum_add_distrib]]
  have hs : (∑ v : V, if e.source = v then
      DirectionStress.edgeDirection a e j else 0) =
      DirectionStress.edgeDirection a e j := by
    have hfun : (fun v : V ↦ if e.source = v then
        DirectionStress.edgeDirection a e j else 0) =
        (fun v : V ↦ if v = e.source then
          DirectionStress.edgeDirection a e j else 0) := by
      funext v
      by_cases h : e.source = v
      · subst v
        simp
      · have hv : v ≠ e.source := Ne.symm h
        simp [h, hv]
    rw [hfun]
    simp
  have ht : (∑ v : V, if e.target = v then
      -DirectionStress.edgeDirection a e j else 0) =
      -DirectionStress.edgeDirection a e j := by
    have hfun : (fun v : V ↦ if e.target = v then
        -DirectionStress.edgeDirection a e j else 0) =
        (fun v : V ↦ if v = e.target then
          -DirectionStress.edgeDirection a e j else 0) := by
      funext v
      by_cases h : e.target = v
      · subst v
        simp
      · have hv : v ≠ e.target := Ne.symm h
        simp [h, hv]
    rw [hfun]
    simp
  rw [hs, ht, add_neg_cancel]

/-- Every synthesized equilibrium load has total vertex load zero. -/
theorem sum_directionEquilibrium_eq_zero
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k) (j : Fin 3) :
    ∑ v : V, DirectionStress.directionEquilibrium F a w v j = 0 := by
  simp only [DirectionStress.directionEquilibrium_apply,
    DirectionStress.directionEquilibriumCoordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _he
  rw [← Finset.mul_sum]
  rw [sum_directionRow_eq_zero, mul_zero]

/-- If all non-root blocks of an equilibrium load vanish, its root block
vanishes automatically. -/
theorem root_equilibrium_eq_zero_of_offRoot_eq_zero
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (w : F → k)
    (haway : ∀ x : OffRoot root,
      DirectionStress.directionEquilibrium F a w x.1 = 0) :
    DirectionStress.directionEquilibrium F a w root = 0 := by
  funext j
  have hsum := sum_directionEquilibrium_eq_zero F a w j
  have hsingle :
      (∑ v : V, DirectionStress.directionEquilibrium F a w v j) =
        DirectionStress.directionEquilibrium F a w root j := by
    rw [Finset.sum_eq_single root]
    · intro v _hv hvr
      have hv := congrFun (haway ⟨v, hvr⟩) j
      exact hv
    · simp
  rw [hsingle] at hsum
  exact hsum

/-- Restricting equilibrium output to non-root blocks preserves the stress
kernel literally. -/
theorem ker_synthesis_eq_directionStressSpace
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    LinearMap.ker (synthesis root F a) =
      DirectionStress.DirectionStressSpace F a := by
  ext w
  simp only [LinearMap.mem_ker]
  constructor
  · intro hw
    funext v j
    by_cases hv : v = root
    · subst v
      exact congrFun
        (root_equilibrium_eq_zero_of_offRoot_eq_zero root F a w
          (fun x ↦ by
            funext q
            have hx := congrFun hw ⟨x, q⟩
            simpa [synthesis_apply] using hx)) j
    · have hx := congrFun hw ⟨⟨v, hv⟩, j⟩
      simpa [synthesis_apply] using hx
  · intro hw
    funext x
    have hx := congrFun (congrFun hw x.1.1) x.2
    simpa [synthesis_apply] using hx

theorem stressDim_eq_directionStressDim
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    FiniteRowSystem.stressDim
        (fun e : F ↦ groundedDirectionRow root a e.1) =
      DirectionStress.directionStressDim F a := by
  change Module.finrank k (LinearMap.ker (synthesis root F a)) =
    Module.finrank k (DirectionStress.DirectionStressSpace F a)
  rw [ker_synthesis_eq_directionStressSpace]

/-- Exact grounded solution/stress ledger. -/
theorem solutionDim_add_edgeCard_eq_groundedCard_add_stressDim
    (root : V) (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    Module.finrank k (LinearMap.ker (constraint root F a)) + F.card =
      Fintype.card (GroundedSpatialCoordinate root) +
        DirectionStress.directionStressDim F a := by
  simpa [constraint, stressDim_eq_directionStressDim] using
    FiniteRowSystem.solutionDim_add_rowCard_eq_coordinateCard_add_stressDim
      (fun e : F ↦ groundedDirectionRow root a e.1)

end

end GroundedDirectionConstraint

end RB31E2E
