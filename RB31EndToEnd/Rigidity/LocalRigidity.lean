import RB31EndToEnd.Rigidity.LengthMap
import RB31EndToEnd.Rigidity.GraphNecessity

/-!
# Maximum rigidity rank implies Euclidean local rigidity

For two edge-equivalent placements, their displacement is an infinitesimal
motion at their midpoint. If the original placement attains the complete
graph's maximum rank, nearby midpoints have equal graph and complete-graph
kernels. The displacement therefore preserves every pairwise distance.
-/

namespace RB31E2E.BarJoint

open scoped Topology

variable {V : Type} [Fintype V] {d : ℕ}

/-- Equal graph and complete-graph ranks give identical motion kernels. -/
theorem ker_rigidityOperator_eq_complete_of_rank_eq
    (G : SimpleGraph V) (p : Placement V d)
    (h : rigidityRank G p = rigidityRank (SimpleGraph.completeGraph V) p) :
    (rigidityOperator G p).ker =
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  have hle : (rigidityOperator (SimpleGraph.completeGraph V) p).ker ≤
      (rigidityOperator G p).ker := by
    intro u hu
    exact BodyPinIncidence.infinitesimalMotion_of_le
      (show G ≤ SimpleGraph.completeGraph V from fun _ _ huv => huv.ne) p u hu
  have hG := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hK := (rigidityOperator (SimpleGraph.completeGraph V) p).finrank_range_add_finrank_ker
  unfold rigidityRank at h
  have hdim : Module.finrank ℝ (rigidityOperator G p).ker ≤
      Module.finrank ℝ (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle hdim).symm

omit [Fintype V] in
/-- The displacement of equivalent placements is a motion at their midpoint. -/
theorem isInfinitesimalMotion_midpoint_of_isEquivalent
    (G : SimpleGraph V) {p q : Placement V d} (h : IsEquivalent G p q) :
    IsInfinitesimalMotion G ((2 : ℝ)⁻¹ • (p + q)) (q - p) := by
  rw [isInfinitesimalMotion_iff]
  intro v w hvw
  have hlen := (isEquivalent_iff_squaredLengthMap_eq G p q).mp h
  have hpq : squaredPairDistance p v w = squaredPairDistance q v w := by
    have he := congrFun hlen (v, w)
    simpa only [squaredLengthMap_apply_of_adj G _ v w hvw] using he
  have hm := squaredPairDistance_sub_eq_two_mul_edgeConstraint_midpoint p q v w
  rw [hpq, sub_self] at hm
  linarith

omit [Fintype V] in
/-- A complete-graph midpoint motion makes the endpoint placements congruent. -/
theorem isCongruent_of_complete_midpoint_motion
    {p q : Placement V d}
    (h : IsInfinitesimalMotion (SimpleGraph.completeGraph V)
      ((2 : ℝ)⁻¹ • (p + q)) (q - p)) : IsCongruent p q := by
  rw [isCongruent_iff_complete_squaredLengthMap_eq]
  funext vw
  by_cases hvw : vw.1 = vw.2
  · have hnot : ¬ (SimpleGraph.completeGraph V).Adj vw.1 vw.2 := by
      simpa using hvw
    simp only [squaredLengthMap_apply_of_not_adj _ _ vw.1 vw.2 hnot]
  · have hadj : (SimpleGraph.completeGraph V).Adj vw.1 vw.2 := hvw
    have hm := (isInfinitesimalMotion_iff _ _ _).mp h vw.1 vw.2 hadj
    have hid := squaredPairDistance_sub_eq_two_mul_edgeConstraint_midpoint p q vw.1 vw.2
    rw [hm, mul_zero] at hid
    simpa only [squaredLengthMap_apply_of_adj _ _ _ _ hadj] using
      (sub_eq_zero.mp hid).symm

/-- Attaining the complete graph's maximum rank implies ordinary local rigidity. -/
theorem isLocallyRigid_of_rigidityRank_eq_complete_genericRank
    (G : SimpleGraph V) (p : Placement V d)
    (hp : rigidityRank G p = genericRigidityRank (SimpleGraph.completeGraph V) d) :
    IsLocallyRigid G p := by
  let r := genericRigidityRank (SimpleGraph.completeGraph V) d
  have hnear : ∀ᶠ m : Placement V d in 𝓝 p, r ≤ rigidityRank G m :=
    (isOpen_setOf_le_rigidityRank G r).mem_nhds hp.ge
  have hcont : Continuous (fun q : Placement V d => (2 : ℝ)⁻¹ • (p + q)) := by
    fun_prop
  have hmid : (2 : ℝ)⁻¹ • (p + p) = p := by
    ext v i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hmidlim : Filter.Tendsto (fun q : Placement V d => (2 : ℝ)⁻¹ • (p + q))
      (𝓝 p) (𝓝 p) := by
    simpa only [hmid] using hcont.continuousAt.tendsto (x := p)
  filter_upwards [hmidlim.eventually hnear] with q hq
  intro heq
  have hmono := BodyPinIncidence.rigidityRank_mono
    (show G ≤ SimpleGraph.completeGraph V from fun _ _ huv => huv.ne)
    ((2 : ℝ)⁻¹ • (p + q))
  have hupper := rigidityRank_le_genericRigidityRank (SimpleGraph.completeGraph V) d
    ((2 : ℝ)⁻¹ • (p + q))
  have hr : rigidityRank G ((2 : ℝ)⁻¹ • (p + q)) =
      rigidityRank (SimpleGraph.completeGraph V) ((2 : ℝ)⁻¹ • (p + q)) := by
    exact le_antisymm hmono (hupper.trans hq)
  have hm := isInfinitesimalMotion_midpoint_of_isEquivalent G heq
  rw [IsInfinitesimalMotion, ker_rigidityOperator_eq_complete_of_rank_eq G _ hr] at hm
  exact isCongruent_of_complete_midpoint_motion hm

end RB31E2E.BarJoint
