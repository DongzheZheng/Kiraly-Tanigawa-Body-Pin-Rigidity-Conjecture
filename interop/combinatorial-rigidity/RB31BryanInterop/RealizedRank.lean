import RB31EndToEnd.Rigidity.BarJoint
import CombinatorialRigidity.Framework

/-!
# Comparing the realized bar--joint rigidity ranks

This module imports both projects' actual rigidity operators. The coordinate
conversion is linear, and the edge-indexed constraints determine the same
kernel as the ordered-pair constraints.
-/

namespace RB31E2E.BryanInterop

open scoped InnerProductSpace

/-- The coordinatewise linear equivalence between the two placement spaces. -/
noncomputable def frameworkEquiv (V : Type) (d : ℕ) :
    BarJoint.Placement V d ≃ₗ[ℝ] SimpleGraph.Framework V d :=
  LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm

@[simp]
theorem frameworkEquiv_apply {V : Type} {d : ℕ}
    (p : BarJoint.Placement V d) (v : V) (i : Fin d) :
    frameworkEquiv V d p v i = p v i := rfl

@[simp]
theorem frameworkEquiv_symm_apply {V : Type} {d : ℕ}
    (p : SimpleGraph.Framework V d) (v : V) (i : Fin d) :
    (frameworkEquiv V d).symm p v i = p v i := rfl

/-- Each Euclidean inner-product constraint is the original coordinate sum. -/
theorem inner_edge_eq {V : Type} {d : ℕ}
    (p : BarJoint.Placement V d) (u : BarJoint.Velocity V d) (v w : V) :
    ⟪frameworkEquiv V d p v - frameworkEquiv V d p w,
      frameworkEquiv V d u v - frameworkEquiv V d u w⟫_ℝ =
      BarJoint.edgeConstraint p u v w := by
  simp [PiLp.inner_apply, BarJoint.edgeConstraint, mul_comm]

/-- The two operators have exactly the same motions after coordinate conversion. -/
theorem mem_ker_rigidityMap_iff {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : BarJoint.Placement V d) (u : BarJoint.Velocity V d) :
    frameworkEquiv V d u ∈ (G.RigidityMap (frameworkEquiv V d p)).ker ↔
      u ∈ (BarJoint.rigidityOperator G p).ker := by
  change _ ↔ BarJoint.IsInfinitesimalMotion G p u
  rw [BarJoint.isInfinitesimalMotion_iff]
  constructor
  · intro hu v w hvw
    have h := congrFun (LinearMap.mem_ker.mp hu) ⟨s(v, w), hvw⟩
    rw [G.rigidityMap_apply (frameworkEquiv V d p) (frameworkEquiv V d u) v w hvw,
      inner_edge_eq] at h
    exact h
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    obtain ⟨e, he⟩ := e
    induction e with
    | h v w =>
      simpa only [SimpleGraph.rigidityMap_apply, inner_edge_eq, Pi.zero_apply] using
        hu v w he

/-- Equality of the realized ranks, for every finite graph and every placement. -/
theorem rigidityRank_eq_finrank_range {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : BarJoint.Placement V d) :
    BarJoint.rigidityRank G p =
      Module.finrank ℝ (LinearMap.range (G.RigidityMap (frameworkEquiv V d p))) := by
  let E := frameworkEquiv V d
  let B := G.RigidityMap (E p)
  have hk : (B.comp E.toLinearMap).ker = (BarJoint.rigidityOperator G p).ker := by
    ext u
    exact mem_ker_rigidityMap_iff G p u
  have hB := (B.comp E.toLinearMap).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp_of_range_eq_top B E.range, hk] at hB
  have hA := (BarJoint.rigidityOperator G p).finrank_range_add_finrank_ker
  change Module.finrank ℝ (BarJoint.rigidityOperator G p).range = _
  exact Nat.add_right_cancel (hA.trans hB.symm)

end RB31E2E.BryanInterop
