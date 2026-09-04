import RB31EndToEnd.Rigidity.LengthMap
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.UnitInterval

/-!
# Connected families of equivalent placements

If every placement congruent to a base placement is locally rigid, a
continuous family of equivalent placements containing the base placement
consists entirely of congruent placements.
-/

namespace RB31E2E.BarJoint

open scoped Topology

variable {V : Type} [Fintype V] {d : ℕ}

/-- Local rigidity throughout a congruence class prevents a connected
continuous family of equivalent placements from leaving that class. -/
theorem isCongruent_along_continuous_family_of_congruent_local
    (G : SimpleGraph V) {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (c : T → Placement V d) (hc : Continuous c) (t₀ : T)
    (hloc : ∀ t, IsCongruent (c t₀) (c t) → IsLocallyRigid G (c t))
    (heq : ∀ t, IsEquivalent G (c t₀) (c t)) :
    ∀ t, IsCongruent (c t₀) (c t) := by
  let K := SimpleGraph.completeGraph V
  let S : Set T := {t | squaredLengthMap K (c t) = squaredLengthMap K (c t₀)}
  have hSclosed : IsClosed S :=
    isClosed_eq ((contDiff_squaredLengthMap K).continuous.comp hc) continuous_const
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hcong : IsCongruent (c t₀) (c t) :=
      (isCongruent_iff_complete_squaredLengthMap_eq _ _).mpr ht.symm
    have hnear : ∀ᶠ s in 𝓝 t,
        IsEquivalent G (c t) (c s) → IsCongruent (c t) (c s) :=
      hc.continuousAt (hloc t hcong)
    filter_upwards [hnear] with s hs
    have heqts : IsEquivalent G (c t) (c s) := by
      apply (isEquivalent_iff_squaredLengthMap_eq G _ _).mpr
      exact ((isEquivalent_iff_squaredLengthMap_eq G _ _).mp (heq t)).symm.trans
        ((isEquivalent_iff_squaredLengthMap_eq G _ _).mp (heq s))
    have hk := (isCongruent_iff_complete_squaredLengthMap_eq _ _).mp (hs heqts)
    exact hk.symm.trans ht
  have hSall : S = Set.univ :=
    IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨t₀, rfl⟩
  intro t
  apply (isCongruent_iff_complete_squaredLengthMap_eq _ _).mpr
  have ht : t ∈ S := hSall ▸ Set.mem_univ t
  exact ht.symm

/-- Every continuous motion on the unit interval which starts at `p` and
preserves graph-edge lengths remains congruent to `p` throughout. -/
def IsContinuouslyRigid (G : SimpleGraph V) (p : Placement V d) : Prop :=
  ∀ c : unitInterval → Placement V d, Continuous c → c 0 = p →
    (∀ t, IsEquivalent G p (c t)) → ∀ t, IsCongruent p (c t)

/-- Continuous rigidity using native Euclidean placements and their topology. -/
def EuclideanIsContinuouslyRigid (G : SimpleGraph V)
    (p : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ c : unitInterval → (V → EuclideanSpace ℝ (Fin d)), Continuous c → c 0 = p →
    (∀ t, EuclideanIsEquivalent G p (c t)) → ∀ t, EuclideanIsCongruent p (c t)

/-- The continuous-motion property is invariant under the coordinate-to-
Euclidean homeomorphism. -/
theorem isContinuouslyRigid_iff_euclideanIsContinuouslyRigid
    (G : SimpleGraph V) (p : Placement V d) :
    IsContinuouslyRigid G p ↔ EuclideanIsContinuouslyRigid G (toEuclideanPlacement p) := by
  let e := placementEuclideanEquiv (V := V) (d := d)
  constructor
  · intro h c hc hzero heq
    let c' : unitInterval → Placement V d := fun t => e.symm (c t)
    have hc' : Continuous c' := e.symm.continuous.comp hc
    have hzero' : c' 0 = p := by
      change e.symm (c 0) = p
      change c 0 = e p at hzero
      rw [hzero, e.symm_apply_apply]
    have heq' : ∀ t, IsEquivalent G p (c' t) := by
      intro t
      change EuclideanIsEquivalent G (e p) (e (e.symm (c t)))
      simpa only [e.apply_symm_apply] using heq t
    have hcong := h c' hc' hzero' heq'
    intro t
    have ht := hcong t
    change EuclideanIsCongruent (e p) (e (e.symm (c t))) at ht
    simpa only [e.apply_symm_apply] using ht
  · intro h c hc hzero heq
    let c' : unitInterval → (V → EuclideanSpace ℝ (Fin d)) := fun t => e (c t)
    have hc' : Continuous c' := e.continuous.comp hc
    have hzero' : c' 0 = toEuclideanPlacement p := by
      change e (c 0) = e p
      rw [hzero]
    have heq' : ∀ t, EuclideanIsEquivalent G (toEuclideanPlacement p) (c' t) := heq
    exact h c' hc' hzero' heq'

end RB31E2E.BarJoint
