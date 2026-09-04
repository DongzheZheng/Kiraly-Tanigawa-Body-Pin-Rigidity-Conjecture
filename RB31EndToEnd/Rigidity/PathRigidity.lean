import RB31EndToEnd.Rigidity.ContinuousRigidity
import RB31EndToEnd.Rigidity.ConnectedMotion

/-!
# Rigidity along continuous motions

A placement attaining the complete graph's maximum rank remains congruent
to itself under every continuous edge-length-preserving motion. The argument
uses rank invariance under congruence and connectedness of the parameter
space. No differentiability of the motion is required.
-/

namespace RB31E2E.BarJoint

open scoped Topology

variable {V : Type} [Fintype V] {d : ℕ}

/-- Every continuous edge-equivalent family on a connected parameter space
is congruent if one of its members attains the complete graph's maximum rank. -/
theorem isCongruent_along_continuous_family_of_maxrank
    (G : SimpleGraph V) {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (c : T → Placement V d) (hc : Continuous c) (t₀ : T)
    (hp : rigidityRank G (c t₀) = genericRigidityRank (SimpleGraph.completeGraph V) d)
    (heq : ∀ t, IsEquivalent G (c t₀) (c t)) :
    ∀ t, IsCongruent (c t₀) (c t) := by
  apply isCongruent_along_continuous_family_of_congruent_local G c hc t₀ _ heq
  intro t hcong
  exact isLocallyRigid_of_rigidityRank_eq_complete_genericRank G (c t)
    ((rigidityRank_eq_of_isCongruent G _ _ hcong).symm.trans hp)

/-- Maximum complete-graph rank excludes all noncongruent continuous motions,
including motions which have no derivative. -/
theorem isContinuouslyRigid_of_rigidityRank_eq_complete_genericRank
    (G : SimpleGraph V) (p : Placement V d)
    (hp : rigidityRank G p = genericRigidityRank (SimpleGraph.completeGraph V) d) :
    IsContinuouslyRigid G p := by
  intro c hc hzero heq
  have hmax : rigidityRank G (c 0) = genericRigidityRank (SimpleGraph.completeGraph V) d := by
    simpa only [hzero] using hp
  have heq' : ∀ t, IsEquivalent G (c 0) (c t) := by
    simpa only [hzero] using heq
  simpa only [hzero] using
    isCongruent_along_continuous_family_of_maxrank G c hc 0 hmax heq'

end RB31E2E.BarJoint
