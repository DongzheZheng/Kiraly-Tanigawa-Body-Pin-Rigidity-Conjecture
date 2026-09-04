import RB31BryanInterop.RealizedRank
import CombinatorialRigidity.GenericRigidityMatroid

/-!
# Comparing the generic bar--joint rigidity ranks

The maximum attained real rank equals the generic rigidity matroid rank in
CombinatorialRigidity. This comparison uses the actual definitions of both
projects and requires neither a positive dimension nor a lower vertex bound.
-/

namespace RB31E2E.BryanInterop

/-- Equality of our maximum attained rank and Bryan's generic matroid rank. -/
theorem genericRigidityRank_eq_genericRank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    BarJoint.genericRigidityRank G d = G.genericRank d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := BarJoint.exists_rigidityRank_eq_genericRigidityRank G d
    calc
      BarJoint.genericRigidityRank G d = BarJoint.rigidityRank G p := hp.symm
      _ = Module.finrank ℝ (G.RigidityMap (frameworkEquiv V d p)).range :=
        rigidityRank_eq_finrank_range G p
      _ ≤ G.genericRank d := G.finrank_range_rigidityMap_le_genericRank _
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_isGenericPlacement (V := V) d
    have h := BarJoint.rigidityRank_le_genericRigidityRank G d
      ((frameworkEquiv V d).symm p)
    rw [rigidityRank_eq_finrank_range, LinearEquiv.apply_symm_apply,
      G.finrank_range_rigidityMap_eq_genericRank hp] at h
    exact h

/-- The maximum-rank rigidity predicate expressed using Bryan's generic rank. -/
theorem isGenericallyRigidInDimension_iff_genericRank_eq_complete
    {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ) :
    BarJoint.IsGenericallyRigidInDimension G d ↔
      G.genericRank d = (SimpleGraph.completeGraph V).genericRank d := by
  unfold BarJoint.IsGenericallyRigidInDimension
  rw [genericRigidityRank_eq_genericRank, genericRigidityRank_eq_genericRank]

end RB31E2E.BryanInterop
