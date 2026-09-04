import RB31EndToEnd.Analysis.RegularFibre
import RB31EndToEnd.Rigidity.LocalRigidity
import RB31EndToEnd.Rigidity.RegularPlacement

/-!
# Generic local rigidity and maximum rigidity rank

At a regular placement, local constancy of all pairwise distances on an
edge-length fibre implies equality of the graph and complete-graph motion
kernels. Conversely, attaining the complete graph's maximum rank implies
local rigidity by the midpoint identity. The open dense regular locus makes
this equivalence a statement about ordinary Euclidean local rigidity.
-/

namespace RB31E2E.BarJoint

open scoped Topology

variable {V : Type} [Fintype V] {d : ℕ}

/-- At a regular locally rigid placement, every infinitesimal motion preserves
all pairwise distances to first order. -/
theorem ker_rigidityOperator_eq_complete_of_isLocallyRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hloc : IsLocallyRigid G p) :
    (rigidityOperator G p).ker =
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  have hmax : ∀ q : Placement V d,
      Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) q).range ≤
        Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) p).range := by
    intro q
    rw [finrank_range_fderiv_squaredLengthMap,
      finrank_range_fderiv_squaredLengthMap]
    exact (rigidityRank_le_genericRigidityRank G d q).trans_eq hp.symm
  have hlevel : ∀ᶠ q in 𝓝 p,
      squaredLengthMap G q = squaredLengthMap G p →
        squaredLengthMap (SimpleGraph.completeGraph V) q =
          squaredLengthMap (SimpleGraph.completeGraph V) p := by
    filter_upwards [hloc] with q hq
    intro heq
    exact ((isCongruent_iff_complete_squaredLengthMap_eq p q).mp
      (hq ((isEquivalent_iff_squaredLengthMap_eq G p q).mpr heq.symm))).symm
  have hker := RB31E2E.ker_fderiv_le_of_eventually_level_imp
    ((contDiff_squaredLengthMap G).of_le (by simp))
    ((contDiff_squaredLengthMap (SimpleGraph.completeGraph V)).of_le (by simp))
    hmax hlevel
  rw [ker_fderiv_squaredLengthMap, ker_fderiv_squaredLengthMap] at hker
  apply le_antisymm hker
  intro u hu
  exact BodyPinIncidence.infinitesimalMotion_of_le
    (show G ≤ SimpleGraph.completeGraph V from fun _ _ huv => huv.ne) p u hu

/-- Local rigidity at a regular placement forces graph and complete-graph
rigidity ranks to agree at that placement. -/
theorem rigidityRank_eq_complete_of_isLocallyRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hloc : IsLocallyRigid G p) :
    rigidityRank G p = rigidityRank (SimpleGraph.completeGraph V) p := by
  have hker := ker_rigidityOperator_eq_complete_of_isLocallyRigid G p hp hloc
  have hG := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hK := (rigidityOperator (SimpleGraph.completeGraph V) p).finrank_range_add_finrank_ker
  rw [hker] at hG
  unfold rigidityRank
  omega

/-- On the common regular locus of the graph and the complete graph, local
rigidity is equivalent to generic infinitesimal rigidity. -/
theorem isLocallyRigid_iff_isGenericallyRigid_of_regular
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p)
    (hK : IsRegularPlacement (SimpleGraph.completeGraph V) p) :
    IsLocallyRigid G p ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · intro hloc
    exact hp.symm.trans ((rigidityRank_eq_complete_of_isLocallyRigid G p hp hloc).trans hK)
  · intro hr
    exact isLocallyRigid_of_rigidityRank_eq_complete_genericRank G p (hp.trans hr)

/-- Generic local rigidity, stated entirely in terms of Euclidean edge lengths
and congruence on an open dense set of placements. -/
def IsGenericallyLocallyRigid (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ U : Set (Placement V d), IsOpen U ∧ Dense U ∧
    ∀ p ∈ U, IsLocallyRigid G p

/-- The maximum-rank formulation and the open-dense geometric formulation of
generic local rigidity are equivalent in every finite dimension. -/
theorem isGenericallyLocallyRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (d : ℕ) :
    IsGenericallyLocallyRigid G d ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    obtain ⟨p, hp, hpU⟩ :=
      (dense_isGenericPlacement (V := V) (d := d)).exists_mem_open hUopen hUdense.nonempty
    exact (isLocallyRigid_iff_isGenericallyRigid_of_regular G p (hp G)
      (hp (SimpleGraph.completeGraph V))).mp (hUrigid p hpU)
  · intro hr
    refine ⟨{p | IsRegularPlacement G p}, isOpen_isRegularPlacement G,
      dense_isRegularPlacement G, ?_⟩
    intro p hp
    exact isLocallyRigid_of_rigidityRank_eq_complete_genericRank G p (hp.trans hr)

/-- In particular, every simultaneously regular placement has the same local
rigidity status as the graph's maximum-rank criterion. -/
theorem isLocallyRigid_iff_of_isGenericPlacement
    (G : SimpleGraph V) (p : Placement V d) (hp : IsGenericPlacement p) :
    IsLocallyRigid G p ↔ IsGenericallyRigidInDimension G d :=
  isLocallyRigid_iff_isGenericallyRigid_of_regular G p (hp G)
    (hp (SimpleGraph.completeGraph V))

/-- The open-dense geometric property using native Euclidean placements. -/
def EuclideanIsGenericallyLocallyRigid (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ U : Set (V → EuclideanSpace ℝ (Fin d)), IsOpen U ∧ Dense U ∧
    ∀ p ∈ U, EuclideanIsLocallyRigid G p

/-- Changing the normed coordinate representation does not change the
open-dense local-rigidity property. -/
theorem isGenericallyLocallyRigid_iff_euclidean
    (G : SimpleGraph V) (d : ℕ) :
    IsGenericallyLocallyRigid G d ↔ EuclideanIsGenericallyLocallyRigid G d := by
  let e := (placementEuclideanEquiv (V := V) (d := d)).toHomeomorph
  constructor
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    refine ⟨e '' U, e.isOpenMap U hUopen,
      e.surjective.denseRange.dense_image e.continuous hUdense, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    exact (isLocallyRigid_iff_euclideanIsLocallyRigid G p).mp (hUrigid p hp)
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    refine ⟨e.symm '' U, e.symm.isOpenMap U hUopen,
      e.symm.surjective.denseRange.dense_image e.symm.continuous hUdense, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    apply (isLocallyRigid_iff_euclideanIsLocallyRigid G (e.symm p)).mpr
    change EuclideanIsLocallyRigid G (e (e.symm p))
    simpa only [e.apply_symm_apply] using hUrigid p hp

/-- Native Euclidean generic local rigidity is equivalent to maximum rank. -/
theorem euclideanIsGenericallyLocallyRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (d : ℕ) :
    EuclideanIsGenericallyLocallyRigid G d ↔ IsGenericallyRigidInDimension G d :=
  (isGenericallyLocallyRigid_iff_euclidean G d).symm.trans
    (isGenericallyLocallyRigid_iff_isGenericallyRigid G d)

end RB31E2E.BarJoint
