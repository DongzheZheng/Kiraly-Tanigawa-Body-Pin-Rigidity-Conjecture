import RB31EndToEnd.Rigidity.AsimowRoth
import RB31EndToEnd.Rigidity.PathRigidity

/-!
# Continuous and infinitesimal rigidity at regular placements

At a regular placement, continuous rigidity forces every infinitesimal graph
motion to preserve all pairwise distances.  A regular-fibre slice supplies
actual edge-length-preserving paths tangent to every infinitesimal motion.
Together with the maximum-rank implication, this identifies continuous,
local, and generic infinitesimal rigidity on the common regular locus.
-/

namespace RB31E2E.BarJoint

open scoped Topology

variable {V : Type} [Fintype V] {d : ℕ}

/-- At a regular continuously rigid placement, graph motions and complete-
graph motions have the same kernel. -/
theorem ker_rigidityOperator_eq_complete_of_isContinuouslyRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hcontinuous : IsContinuouslyRigid G p) :
    (rigidityOperator G p).ker =
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  let K := SimpleGraph.completeGraph V
  have hmax : ∀ q : Placement V d,
      Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) q).range ≤
        Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) p).range := by
    intro q
    rw [finrank_range_fderiv_squaredLengthMap,
      finrank_range_fderiv_squaredLengthMap]
    exact (rigidityRank_le_genericRigidityRank G d q).trans_eq hp.symm
  obtain ⟨s, ψ, ε, hε, hψ0, hψdiff, hψcont, hfibre, htangent⟩ :=
    RB31E2E.exists_regular_fibre_slice
      ((contDiff_squaredLengthMap G).of_le (by simp)) hmax
  have hscaled_mem (z : Fin s → ℝ) (hz : z ∈ Metric.ball 0 ε)
      (t : unitInterval) : (t : ℝ) • z ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg t.property.1]
    have hz' : ‖z‖ < ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact (mul_le_of_le_one_left (norm_nonneg z) t.property.2).trans_lt hz'
  have hcomplete_fibre : ∀ z ∈ Metric.ball (0 : Fin s → ℝ) ε,
      squaredLengthMap K (ψ z) = squaredLengthMap K p := by
    intro z hz
    let c : unitInterval → Placement V d := fun t ↦ ψ ((t : ℝ) • z)
    have hc : Continuous c := by
      change Continuous (ψ ∘ fun t : unitInterval ↦ (t : ℝ) • z)
      exact hψcont.comp_continuous (by fun_prop) (hscaled_mem z hz)
    have hc0 : c 0 = p := by simp [c, hψ0]
    have hceq : ∀ t, IsEquivalent G p (c t) := by
      intro t
      apply (isEquivalent_iff_squaredLengthMap_eq G p (c t)).mpr
      exact (hfibre _ (hscaled_mem z hz t)).symm
    have hcong := hcontinuous c hc hc0 hceq (1 : unitInterval)
    have hcong' : IsCongruent p (ψ z) := by
      simpa [c] using hcong
    exact ((isCongruent_iff_complete_squaredLengthMap_eq p (ψ z)).mp hcong').symm
  have hcomplete_eventually :
      (fun z : Fin s → ℝ ↦ squaredLengthMap K (ψ z)) =ᶠ[nhds (0 : Fin s → ℝ)]
        (fun _ ↦ squaredLengthMap K p) := by
    filter_upwards [Metric.ball_mem_nhds 0 hε] with z hz
    exact hcomplete_fibre z hz
  have hcomplete_comp : HasFDerivAt
      (fun z : Fin s → ℝ ↦ squaredLengthMap K (ψ z))
      ((fderiv ℝ (squaredLengthMap K) p).comp (fderiv ℝ ψ 0)) 0 := by
    have hKp : HasFDerivAt (squaredLengthMap K)
        (fderiv ℝ (squaredLengthMap K) p) (ψ 0) := by
      simpa only [hψ0] using
        (((contDiff_squaredLengthMap K).of_le (by simp)).differentiable_one p).hasFDerivAt
    exact hKp.comp 0 hψdiff.hasFDerivAt
  have hcomplete_comp_zero :
      (fderiv ℝ (squaredLengthMap K) p).comp (fderiv ℝ ψ 0) = 0 :=
    hcomplete_comp.unique
      (hasFDerivAt_zero_of_eventually_const (squaredLengthMap K p)
        hcomplete_eventually)
  have hker : (fderiv ℝ (squaredLengthMap G) p).ker ≤
      (fderiv ℝ (squaredLengthMap K) p).ker := by
    intro v hv
    rcases htangent hv with ⟨z, hz⟩
    rw [LinearMap.mem_ker]
    have hzero := DFunLike.congr_fun hcomplete_comp_zero z
    change fderiv ℝ (squaredLengthMap K) p (fderiv ℝ ψ 0 z) = 0 at hzero
    calc
      fderiv ℝ (squaredLengthMap K) p v =
          fderiv ℝ (squaredLengthMap K) p (fderiv ℝ ψ 0 z) :=
        congrArg (fderiv ℝ (squaredLengthMap K) p) hz.symm
      _ = 0 := hzero
  rw [ker_fderiv_squaredLengthMap, ker_fderiv_squaredLengthMap] at hker
  apply le_antisymm hker
  intro u hu
  exact BodyPinIncidence.infinitesimalMotion_of_le
    (show G ≤ SimpleGraph.completeGraph V from fun _ _ huv => huv.ne) p u hu

/-- Continuous rigidity at a regular placement forces equality of the graph
and complete-graph rigidity ranks there. -/
theorem rigidityRank_eq_complete_of_isContinuouslyRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hcontinuous : IsContinuouslyRigid G p) :
    rigidityRank G p = rigidityRank (SimpleGraph.completeGraph V) p := by
  have hker := ker_rigidityOperator_eq_complete_of_isContinuouslyRigid
    G p hp hcontinuous
  have hG := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hK :=
    (rigidityOperator (SimpleGraph.completeGraph V) p).finrank_range_add_finrank_ker
  rw [hker] at hG
  unfold rigidityRank
  omega

/-- On the common regular locus, continuous rigidity is equivalent to the
maximum-rank generic rigidity criterion. -/
theorem isContinuouslyRigid_iff_isGenericallyRigid_of_regular
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p)
    (hK : IsRegularPlacement (SimpleGraph.completeGraph V) p) :
    IsContinuouslyRigid G p ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · intro hcontinuous
    exact hp.symm.trans
      ((rigidityRank_eq_complete_of_isContinuouslyRigid G p hp hcontinuous).trans hK)
  · intro hr
    exact isContinuouslyRigid_of_rigidityRank_eq_complete_genericRank G p
      (hp.trans hr)

/-- At a placement regular for both the graph and the complete graph,
continuous rigidity and local rigidity agree. -/
theorem isContinuouslyRigid_iff_isLocallyRigid_of_regular
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p)
    (hK : IsRegularPlacement (SimpleGraph.completeGraph V) p) :
    IsContinuouslyRigid G p ↔ IsLocallyRigid G p :=
  (isContinuouslyRigid_iff_isGenericallyRigid_of_regular G p hp hK).trans
    (isLocallyRigid_iff_isGenericallyRigid_of_regular G p hp hK).symm

/-- A graph is generically continuously rigid when continuous rigidity holds
on an open dense set of placements. -/
def IsGenericallyContinuouslyRigid (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ U : Set (Placement V d), IsOpen U ∧ Dense U ∧
    ∀ p ∈ U, IsContinuouslyRigid G p

/-- Generic continuous rigidity is equivalent to the maximum-rank rigidity
criterion. -/
theorem isGenericallyContinuouslyRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (d : ℕ) :
    IsGenericallyContinuouslyRigid G d ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    obtain ⟨p, hp, hpU⟩ :=
      (dense_isGenericPlacement (V := V) (d := d)).exists_mem_open
        hUopen hUdense.nonempty
    exact (isContinuouslyRigid_iff_isGenericallyRigid_of_regular G p (hp G)
      (hp (SimpleGraph.completeGraph V))).mp (hUrigid p hpU)
  · intro hr
    refine ⟨{p | IsRegularPlacement G p}, isOpen_isRegularPlacement G,
      dense_isRegularPlacement G, ?_⟩
    intro p hp
    exact isContinuouslyRigid_of_rigidityRank_eq_complete_genericRank G p
      (hp.trans hr)

end RB31E2E.BarJoint
