import RB31EndToEnd.Rigidity.BarJoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Squared edge lengths and local rigidity

The bar--joint rigidity operator is the derivative, up to the conventional
factor `2`, of the squared edge-length map.  Distances in this file are the
Euclidean distances obtained from the `L²` norm on coordinate space.
-/

namespace RB31E2E
namespace BarJoint

open scoped BigOperators

/-- Regard a coordinate vector as a point of Euclidean space. -/
def toEuclideanPoint {d : ℕ} (x : Point d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 x

/-- Regard a coordinate placement as a Euclidean placement. -/
def toEuclideanPlacement {V : Type} {d : ℕ} (p : Placement V d) :
    V → EuclideanSpace ℝ (Fin d) :=
  fun v ↦ toEuclideanPoint (p v)

/-- The coordinate placement space and the Euclidean `L²` placement space
are continuously linearly equivalent. -/
noncomputable def placementEuclideanEquiv
    {V : Type} [Fintype V] {d : ℕ} :
    Placement V d ≃L[ℝ] (V → EuclideanSpace ℝ (Fin d)) :=
  ContinuousLinearEquiv.piCongrRight fun _ : V ↦
    (EuclideanSpace.equiv (Fin d) ℝ).symm

@[simp] theorem placementEuclideanEquiv_apply
    {V : Type} [Fintype V] {d : ℕ} (p : Placement V d) :
    placementEuclideanEquiv p = toEuclideanPlacement p :=
  rfl

@[simp] theorem placementEuclideanEquiv_symm_apply
    {V : Type} [Fintype V] {d : ℕ}
    (p : V → EuclideanSpace ℝ (Fin d)) :
    (placementEuclideanEquiv.symm p : Placement V d) = fun v i ↦ p v i :=
  rfl

/-- The equivalence carries coordinate-space neighbourhoods to Euclidean
placement-space neighbourhoods. -/
theorem placementEuclideanEquiv_map_nhds
    {V : Type} [Fintype V] {d : ℕ} (p : Placement V d) :
    Filter.map placementEuclideanEquiv (nhds p) =
      nhds (toEuclideanPlacement p) := by
  simpa using (placementEuclideanEquiv (V := V) (d := d)).map_nhds_eq p

/-- The squared Euclidean distance between two vertices of a placement. -/
def squaredPairDistance {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) : ℝ :=
  ∑ i : Fin d, (p v i - p w i) ^ 2

/-- The squared edge-length map.  Coordinates indexed by nonedges are zero. -/
noncomputable def squaredLengthMap {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : V × V → ℝ := by
  classical
  exact fun vw ↦
    if G.Adj vw.1 vw.2 then squaredPairDistance p vw.1 vw.2 else 0

@[simp] theorem squaredLengthMap_apply_of_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (v w : V) (h : G.Adj v w) :
    squaredLengthMap G p (v, w) = squaredPairDistance p v w := by
  simp [squaredLengthMap, h]

@[simp] theorem squaredLengthMap_apply_of_not_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (v w : V) (h : ¬ G.Adj v w) :
    squaredLengthMap G p (v, w) = 0 := by
  simp [squaredLengthMap, h]

/-- The coordinate formula for `squaredPairDistance` is the square of the
genuine Euclidean `L²` distance. -/
theorem squaredPairDistance_eq_sq_dist_toEuclidean {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) :
    squaredPairDistance p v w =
      dist (toEuclideanPoint (p v)) (toEuclideanPoint (p w)) ^ 2 := by
  simpa [squaredPairDistance, toEuclideanPoint, Real.dist_eq, sq_abs] using
    (EuclideanSpace.dist_sq_eq
      (toEuclideanPoint (p v)) (toEuclideanPoint (p w))).symm

theorem squaredPairDistance_eq_iff_euclidean_dist_eq
    {V : Type} {d : ℕ} (p q : Placement V d) (v w : V) :
    squaredPairDistance p v w = squaredPairDistance q v w ↔
      dist (toEuclideanPoint (p v)) (toEuclideanPoint (p w)) =
        dist (toEuclideanPoint (q v)) (toEuclideanPoint (q w)) := by
  rw [squaredPairDistance_eq_sq_dist_toEuclidean,
    squaredPairDistance_eq_sq_dist_toEuclidean,
    sq_eq_sq₀ dist_nonneg dist_nonneg]

private noncomputable def coordinateDifferenceCLM
    {V : Type} [Fintype V] {d : ℕ} (v w : V) (i : Fin d) :
    Placement V d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ p v i - p w i
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }

private noncomputable def edgeFunctionalCLM
    {V : Type} [Fintype V] {d : ℕ} (p : Placement V d) (v w : V) :
    Velocity V d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (edgeFunctional p v w)

/-- The rigidity operator, regarded as a continuous linear map. -/
noncomputable def rigidityOperatorCLM
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) : Velocity V d →L[ℝ] (V × V → ℝ) :=
  LinearMap.toContinuousLinearMap (rigidityOperator G p)

@[simp] theorem rigidityOperatorCLM_apply
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) (u : Velocity V d) (vw : V × V) :
    rigidityOperatorCLM G p u vw = rigidityOperator G p u vw :=
  rfl

private theorem hasStrictFDerivAt_squaredPairDistance
    {V : Type} [Fintype V] {d : ℕ} (p : Placement V d) (v w : V) :
    HasStrictFDerivAt (fun q : Placement V d ↦ squaredPairDistance q v w)
      ((2 : ℝ) • edgeFunctionalCLM p v w) p := by
  have hsum : HasStrictFDerivAt
      (fun q : Placement V d ↦ ∑ i : Fin d, (q v i - q w i) ^ 2)
      (∑ i : Fin d,
        ((2 : ℝ) • (p v i - p w i)) • coordinateDifferenceCLM v w i) p := by
    apply HasStrictFDerivAt.fun_sum
    intro i _
    simpa [coordinateDifferenceCLM, pow_one, nsmul_eq_mul] using
      (coordinateDifferenceCLM v w i).hasStrictFDerivAt.pow 2
  rw [show (fun q : Placement V d ↦ squaredPairDistance q v w) =
      (fun q : Placement V d ↦ ∑ i : Fin d, (q v i - q w i) ^ 2) by
        rfl]
  exact hsum.congr_fderiv (by
    ext u
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      coordinateDifferenceCLM, edgeFunctionalCLM,
      LinearMap.coe_toContinuousLinearMap', edgeFunctional_apply,
      edgeConstraint, smul_eq_mul]
    change (∑ i : Fin d,
      2 * (p v i - p w i) * (u v i - u w i)) =
        2 * ∑ i : Fin d, (p v i - p w i) * (u v i - u w i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring)

/-- The derivative of the squared edge-length map is twice the rigidity
operator. -/
theorem hasStrictFDerivAt_squaredLengthMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) :
    HasStrictFDerivAt (squaredLengthMap G)
      ((2 : ℝ) • rigidityOperatorCLM G p) p := by
  rw [hasStrictFDerivAt_pi']
  rintro ⟨v, w⟩
  by_cases h : G.Adj v w
  · have hp := hasStrictFDerivAt_squaredPairDistance p v w
    rw [show (fun q : Placement V d ↦ squaredLengthMap G q (v, w)) =
        (fun q : Placement V d ↦ squaredPairDistance q v w) by
          funext q
          simp [squaredLengthMap, h]]
    exact hp.congr_fderiv (by
      ext u
      change 2 * edgeConstraint p u v w =
        2 * rigidityOperator G p u (v, w)
      rw [rigidityOperator_apply_of_adj G p u v w h])
  · rw [show (fun q : Placement V d ↦ squaredLengthMap G q (v, w)) =
        (fun _ : Placement V d ↦ (0 : ℝ)) by
          funext q
          simp [squaredLengthMap, h]]
    exact (hasStrictFDerivAt_const (0 : ℝ) p).congr_fderiv (by
      ext u
      change 0 = 2 * rigidityOperator G p u (v, w)
      rw [rigidityOperator_apply_of_not_adj G p u v w h]
      simp)

theorem fderiv_squaredLengthMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) :
    fderiv ℝ (squaredLengthMap G) p =
      (2 : ℝ) • rigidityOperatorCLM G p :=
  (hasStrictFDerivAt_squaredLengthMap G p).hasFDerivAt.fderiv

/-- The nonlinear length map and the rigidity operator have the same
infinitesimal motions at every placement. -/
theorem ker_fderiv_squaredLengthMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) :
    LinearMap.ker
        (fderiv ℝ (squaredLengthMap G) p :
          Velocity V d →ₗ[ℝ] (V × V → ℝ)) =
      LinearMap.ker (rigidityOperator G p) := by
  rw [fderiv_squaredLengthMap]
  simpa [rigidityOperatorCLM] using
    (LinearMap.ker_smul (rigidityOperator G p) (2 : ℝ) (by norm_num))

/-- The differential of the squared length map has the rigidity rank. -/
theorem finrank_range_fderiv_squaredLengthMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) :
    Module.finrank ℝ
        (LinearMap.range
          ((fderiv ℝ (squaredLengthMap G) p) :
            Velocity V d →ₗ[ℝ] (V × V → ℝ))) =
      rigidityRank G p := by
  rw [fderiv_squaredLengthMap, rigidityRank]
  simpa [rigidityOperatorCLM] using
    congrArg
      (fun S : Submodule ℝ (V × V → ℝ) ↦ Module.finrank ℝ S)
      (LinearMap.range_smul (rigidityOperator G p) (2 : ℝ) (by norm_num))

/-- The squared edge-length map is a polynomial map, hence smooth. -/
theorem contDiff_squaredLengthMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) :
    ContDiff ℝ ⊤ (squaredLengthMap (d := d) G) := by
  rw [contDiff_pi]
  intro vw
  by_cases h : G.Adj vw.1 vw.2
  · rw [show (fun q : Placement V d ↦ squaredLengthMap G q vw) =
        (fun q : Placement V d ↦
          ∑ i : Fin d, (q vw.1 i - q vw.2 i) ^ 2) by
          funext q
          simp [squaredLengthMap, squaredPairDistance, h]]
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply_apply ℝ ℝ vw.1 i).sub
      (contDiff_apply_apply ℝ ℝ vw.2 i)).pow 2
  · rw [show (fun q : Placement V d ↦ squaredLengthMap G q vw) =
        (fun _ : Placement V d ↦ (0 : ℝ)) by
          funext q
          simp [squaredLengthMap, h]]
    exact contDiff_const

/-- Two placements are equivalent if corresponding graph edges have the same
Euclidean length. -/
def IsEquivalent {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p q : Placement V d) : Prop :=
  ∀ v w : V, G.Adj v w →
    dist (toEuclideanPoint (p v)) (toEuclideanPoint (p w)) =
      dist (toEuclideanPoint (q v)) (toEuclideanPoint (q w))

/-- Two labelled placements are congruent if every pairwise Euclidean
distance agrees. -/
def IsCongruent {V : Type} {d : ℕ} (p q : Placement V d) : Prop :=
  ∀ v w : V,
    dist (toEuclideanPoint (p v)) (toEuclideanPoint (p w)) =
      dist (toEuclideanPoint (q v)) (toEuclideanPoint (q w))

/-- Edge-length equivalence stated directly on Euclidean `L²` placements. -/
def EuclideanIsEquivalent {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p q : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ v w : V, G.Adj v w → dist (p v) (p w) = dist (q v) (q w)

/-- Congruence stated directly on Euclidean `L²` placements. -/
def EuclideanIsCongruent {V : Type} {d : ℕ}
    (p q : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ v w : V, dist (p v) (p w) = dist (q v) (q w)

theorem isEquivalent_iff_euclideanIsEquivalent
    {V : Type} {d : ℕ} (G : SimpleGraph V) (p q : Placement V d) :
    IsEquivalent G p q ↔
      EuclideanIsEquivalent G (toEuclideanPlacement p) (toEuclideanPlacement q) :=
  Iff.rfl

theorem isCongruent_iff_euclideanIsCongruent
    {V : Type} {d : ℕ} (p q : Placement V d) :
    IsCongruent p q ↔
      EuclideanIsCongruent (toEuclideanPlacement p) (toEuclideanPlacement q) :=
  Iff.rfl

theorem isEquivalent_iff_squaredLengthMap_eq
    {V : Type} {d : ℕ} (G : SimpleGraph V) (p q : Placement V d) :
    IsEquivalent G p q ↔ squaredLengthMap G p = squaredLengthMap G q := by
  constructor
  · intro h
    funext vw
    by_cases hadj : G.Adj vw.1 vw.2
    · simp only [squaredLengthMap_apply_of_adj G _ _ _ hadj]
      exact (squaredPairDistance_eq_iff_euclidean_dist_eq
        p q vw.1 vw.2).2 (h vw.1 vw.2 hadj)
    · simp [squaredLengthMap, hadj]
  · intro h v w hvw
    have hat := congrFun h (v, w)
    simp only [squaredLengthMap_apply_of_adj G _ _ _ hvw] at hat
    exact (squaredPairDistance_eq_iff_euclidean_dist_eq p q v w).1 hat

theorem isEquivalent_completeGraph_iff_isCongruent
    {V : Type} {d : ℕ} (p q : Placement V d) :
    IsEquivalent (⊤ : SimpleGraph V) p q ↔ IsCongruent p q := by
  constructor
  · intro h v w
    by_cases hvw : v = w
    · subst w
      simp
    · exact h v w (by simpa using hvw)
  · intro h v w _
    exact h v w

theorem isCongruent_iff_complete_squaredLengthMap_eq
    {V : Type} {d : ℕ} (p q : Placement V d) :
    IsCongruent p q ↔
      squaredLengthMap (⊤ : SimpleGraph V) p = squaredLengthMap ⊤ q := by
  rw [← isEquivalent_completeGraph_iff_isCongruent,
    isEquivalent_iff_squaredLengthMap_eq]

/-- A framework is locally rigid when every sufficiently close equivalent
placement is congruent to it. -/
def IsLocallyRigid {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) : Prop :=
  ∀ᶠ q in nhds p, IsEquivalent G p q → IsCongruent p q

/-- Local rigidity formulated in the native topology of Euclidean `L²`
placements. -/
def EuclideanIsLocallyRigid {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ᶠ q in nhds p, EuclideanIsEquivalent G p q → EuclideanIsCongruent p q

/-- The coordinate and Euclidean formulations of local rigidity agree. -/
theorem isLocallyRigid_iff_euclideanIsLocallyRigid
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) :
    IsLocallyRigid G p ↔
      EuclideanIsLocallyRigid G (toEuclideanPlacement p) := by
  rw [IsLocallyRigid, EuclideanIsLocallyRigid,
    ← placementEuclideanEquiv_map_nhds p, Filter.eventually_map]
  rfl

@[simp] theorem completeGraph_isLocallyRigid
    {V : Type} {d : ℕ} (p : Placement V d) :
    IsLocallyRigid (⊤ : SimpleGraph V) p := by
  filter_upwards with q
  exact (isEquivalent_completeGraph_iff_isCongruent p q).mp

/-- Polarization at the midpoint: a finite change in squared pair distance is
the corresponding rigidity row evaluated at the displacement. -/
theorem squaredPairDistance_sub_eq_two_mul_edgeConstraint_midpoint
    {V : Type} {d : ℕ} (p q : Placement V d) (v w : V) :
    squaredPairDistance q v w - squaredPairDistance p v w =
      2 * edgeConstraint ((2 : ℝ)⁻¹ • (p + q)) (q - p) v w := by
  simp only [squaredPairDistance, edgeConstraint, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end BarJoint
end RB31E2E
