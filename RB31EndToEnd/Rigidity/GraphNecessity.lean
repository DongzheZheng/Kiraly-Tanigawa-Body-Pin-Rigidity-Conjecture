import RB31EndToEnd.Rigidity.TwistNecessity
import RB31EndToEnd.Rigidity.BodyTwistGenericBridge
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Generic graph rigidity forces the body--pin partition inequalities

The only delicate step is obtaining a maximum-rank placement whose private
tetrahedral cores are simultaneously nondegenerate.  Rank at least a fixed
value is open because the rigidity operator depends continuously and linearly
on the placement.  Along the line from a rank-attaining placement to the
standard-core placement, degeneracy of each core is the zero set of an
explicit nonzero univariate determinant polynomial.  Finitely many finite
root sets cannot cover a small open interval in the rank-open set.
-/

namespace RB31E2E

namespace BarJoint

/-- With the velocity held fixed, the rigidity operator is linear in the
placement coordinates. -/
noncomputable def rigidityOperatorLinearInPlacement
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) :
    Placement V d →ₗ[ℝ] (Velocity V d →ₗ[ℝ] (V × V → ℝ)) where
  toFun := rigidityOperator G
  map_add' p q := by
    apply LinearMap.ext
    intro u
    funext vw
    classical
    by_cases h : G.Adj vw.1 vw.2
    · simp only [LinearMap.add_apply, Pi.add_apply,
        rigidityOperator_apply_of_adj G _ _ _ _ h, edgeConstraint]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp [rigidityOperator_apply_of_not_adj G _ _ _ _ h]
  map_smul' a p := by
    apply LinearMap.ext
    intro u
    funext vw
    classical
    by_cases h : G.Adj vw.1 vw.2
    · simp only [LinearMap.smul_apply, Pi.smul_apply,
        rigidityOperator_apply_of_adj G _ _ _ _ h, edgeConstraint,
        smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp [rigidityOperator_apply_of_not_adj G _ _ _ _ h]

/-- The rigidity operator as a continuous map from placements to continuous
linear maps on velocities.  Both conversions are legitimate because the
source spaces are finite-dimensional. -/
noncomputable def continuousRigidityOperatorMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) :
    Placement V d →L[ℝ] (Velocity V d →L[ℝ] (V × V → ℝ)) := by
  let inner : (Velocity V d →ₗ[ℝ] (V × V → ℝ)) ≃ₗ[ℝ]
      (Velocity V d →L[ℝ] (V × V → ℝ)) :=
    LinearMap.toContinuousLinearMap
  exact LinearMap.toContinuousLinearMap
    (inner.toLinearMap.comp (rigidityOperatorLinearInPlacement G))

@[simp] theorem continuousRigidityOperatorMap_apply
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) (u : Velocity V d) (vw : V × V) :
    continuousRigidityOperatorMap G p u vw = rigidityOperator G p u vw :=
  rfl

/-- A fixed lower bound on rigidity rank is an open condition on placements. -/
theorem isOpen_setOf_le_rigidityRank
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) (r : ℕ) :
    IsOpen {p : Placement V d | r ≤ rigidityRank G p} := by
  let F := continuousRigidityOperatorMap (d := d) G
  have hopen : IsOpen
      (F ⁻¹' {L : Velocity V d →L[ℝ] (V × V → ℝ) |
        (r : Cardinal) ≤ (L : Velocity V d →ₗ[ℝ] (V × V → ℝ)).rank}) :=
    (isOpen_setOf_nat_le_rank (E := Velocity V d) (F := V × V → ℝ) r).preimage
      F.continuous
  convert hopen using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  change r ≤ Module.finrank ℝ (rigidityOperator G p).range ↔
    (r : Cardinal) ≤ Module.rank ℝ (rigidityOperator G p).range
  rw [← Module.finrank_eq_rank]
  norm_cast

end BarJoint

namespace BodyPinIncidence

/-- The three displacement columns based at vertex `0` of a labelled
tetrahedron. -/
def affineDifferenceMatrix (q : Fin 4 → Vec3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ q (Fin.succ j) i - q 0 i

/-- In three-space, the four labelled points are affine-independent exactly
when their displacement determinant is nonzero. -/
theorem affineIndependent_four_iff_det_affineDifferenceMatrix_ne_zero
    (q : Fin 4 → Vec3 ℝ) :
    AffineIndependent ℝ q ↔ (affineDifferenceMatrix q).det ≠ 0 := by
  let e : Fin 3 ≃ {i : Fin 4 // i ≠ 0} := finSuccAboveEquiv 0
  have hcols : (affineDifferenceMatrix q).col =
      fun j : Fin 3 ↦ q (Fin.succ j) - q 0 := by
    funext j i
    rfl
  constructor
  · intro hq
    have hsub : LinearIndependent ℝ
        (fun i : {i : Fin 4 // i ≠ 0} ↦ q i.1 - q 0) :=
      (affineIndependent_iff_linearIndependent_vsub ℝ q 0).mp hq
    have hfin : LinearIndependent ℝ
        (fun j : Fin 3 ↦ q (Fin.succ j) - q 0) := by
      have := (linearIndependent_equiv e).mpr hsub
      simpa [e, Function.comp_apply, finSuccAboveEquiv_apply,
        Fin.succAbove_zero] using this
    have hunit : IsUnit (affineDifferenceMatrix q) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp (by simpa [hcols] using hfin)
    exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det (affineDifferenceMatrix q)).mp hunit)
  · intro hdet
    have hunitDet : IsUnit (affineDifferenceMatrix q).det :=
      isUnit_iff_ne_zero.mpr hdet
    have hunit : IsUnit (affineDifferenceMatrix q) :=
      (Matrix.isUnit_iff_isUnit_det (affineDifferenceMatrix q)).mpr hunitDet
    have hfin : LinearIndependent ℝ
        (fun j : Fin 3 ↦ q (Fin.succ j) - q 0) := by
      have := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
      simpa [hcols] using this
    have hsub : LinearIndependent ℝ
        (fun i : {i : Fin 4 // i ≠ 0} ↦ q i.1 - q 0) := by
      apply (linearIndependent_equiv e).mp
      simpa [e, Function.comp_apply, finSuccAboveEquiv_apply,
        Fin.succAbove_zero] using hfin
    exact (affineIndependent_iff_linearIndependent_vsub ℝ q 0).mpr hsub

/-- Affine interpolation of two expanded placements. -/
def placementLine {V : Type} (p q : BarJoint.Placement V 3) (t : ℝ) :
    BarJoint.Placement V 3 :=
  (1 - t) • p + t • q

@[simp] theorem placementLine_zero {V : Type}
    (p q : BarJoint.Placement V 3) : placementLine p q 0 = p := by
  simp [placementLine]

@[simp] theorem placementLine_one {V : Type}
    (p q : BarJoint.Placement V 3) : placementLine p q 1 = q := by
  simp [placementLine]

/-- The scalar affine line from `a` to `b`, encoded as a real polynomial. -/
noncomputable def affineLinePolynomial (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.X * Polynomial.C (b - a)

@[simp] theorem eval_affineLinePolynomial (a b t : ℝ) :
    Polynomial.eval t (affineLinePolynomial a b) = (1 - t) * a + t * b := by
  simp [affineLinePolynomial]
  ring

/-- Polynomial displacement matrix of one core along a placement line. -/
noncomputable def coreLinePolynomialMatrix {V : Type}
    (p q : BarJoint.Placement V 3) (f : Fin 4 → V) :
    Matrix (Fin 3) (Fin 3) (Polynomial ℝ) :=
  fun i j ↦ affineLinePolynomial
    (p (f (Fin.succ j)) i - p (f 0) i)
    (q (f (Fin.succ j)) i - q (f 0) i)

/-- The determinant polynomial detecting degeneracy of one core. -/
noncomputable def coreLineDetPolynomial {V : Type}
    (p q : BarJoint.Placement V 3) (f : Fin 4 → V) : Polynomial ℝ :=
  (coreLinePolynomialMatrix p q f).det

theorem eval_coreLineDetPolynomial {V : Type}
    (p q : BarJoint.Placement V 3) (f : Fin 4 → V) (t : ℝ) :
    Polynomial.eval t (coreLineDetPolynomial p q f) =
      (affineDifferenceMatrix (placementLine p q t ∘ f)).det := by
  rw [coreLineDetPolynomial]
  change (Polynomial.evalRingHom t) (coreLinePolynomialMatrix p q f).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [coreLinePolynomialMatrix, affineDifferenceMatrix, placementLine,
    Function.comp_apply]
  ring

theorem coreLineDetPolynomial_ne_zero_of_target_affineIndependent
    {V : Type} (p q : BarJoint.Placement V 3) (f : Fin 4 → V)
    (hq : AffineIndependent ℝ (q ∘ f)) :
    coreLineDetPolynomial p q f ≠ 0 := by
  intro hzero
  have hAt := congrArg (Polynomial.eval 1) hzero
  rw [eval_coreLineDetPolynomial] at hAt
  simp only [placementLine_one, Polynomial.eval_zero] at hAt
  exact (affineIndependent_four_iff_det_affineDifferenceMatrix_ne_zero
    (q ∘ f)).mp hq hAt

/-- The finite union of exceptional line parameters at which at least one
private core degenerates. -/
noncomputable def coreBadParameters (H : BodyPinIncidence)
    (extra : H.Body → ℕ)
    (p q : BarJoint.Placement (H.BPVertex extra) 3) : Finset ℝ :=
  Finset.univ.biUnion fun b ↦
    (coreLineDetPolynomial p q (H.privateCoreVertex extra b)).roots.toFinset

/-- Every nonempty rank-open neighbourhood contains a placement whose private
cores are all affine-independent.  The proof is an explicit one-parameter
finite-root avoidance argument. -/
theorem exists_mem_open_allCoresAffinelyIndependent
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p q : BarJoint.Placement (H.BPVertex extra) 3)
    (hq : H.AllCoresAffinelyIndependent extra q)
    (U : Set (BarJoint.Placement (H.BPVertex extra) 3))
    (hU : IsOpen U) (hp : p ∈ U) :
    ∃ r ∈ U, H.AllCoresAffinelyIndependent extra r := by
  classical
  have hline : Continuous fun t : ℝ ↦ placementLine p q t := by
    unfold placementLine
    fun_prop
  have hopen : IsOpen ((fun t : ℝ ↦ placementLine p q t) ⁻¹' U) :=
    hU.preimage hline
  have hzero : (0 : ℝ) ∈ (fun t : ℝ ↦ placementLine p q t) ⁻¹' U := by
    simpa using hp
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  have hinter : (Set.Ioo (-ε / 2) (ε / 2) : Set ℝ).Infinite := by
    apply Set.Ioo_infinite
    linarith
  obtain ⟨t, ht, htbad⟩ :=
    hinter.exists_notMem_finset (H.coreBadParameters extra p q)
  refine ⟨placementLine p q t, ?_, ?_⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  · intro b
    let P := coreLineDetPolynomial p q (H.privateCoreVertex extra b)
    have hP : P ≠ 0 := by
      apply coreLineDetPolynomial_ne_zero_of_target_affineIndependent
      simpa [P, coreCoordinates, Function.comp_apply] using hq b
    have htRoots : t ∉ P.roots.toFinset := by
      intro htP
      apply htbad
      simp only [coreBadParameters, Finset.mem_biUnion, Finset.mem_univ,
        Multiset.mem_toFinset, true_and]
      exact ⟨b, by simpa [P] using htP⟩
    have hEval : Polynomial.eval t P ≠ 0 := by
      intro hzeroEval
      apply htRoots
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).2 hzeroEval)
    apply (affineIndependent_four_iff_det_affineDifferenceMatrix_ne_zero
      (H.coreCoordinates extra (placementLine p q t) b)).2
    change (affineDifferenceMatrix
      (placementLine p q t ∘ H.privateCoreVertex extra b)).det ≠ 0
    rw [← eval_coreLineDetPolynomial p q (H.privateCoreVertex extra b) t]
    simpa [P] using hEval

/-- The maximum rigidity rank is attained at a placement whose canonical
private cores are all affine-independent.  This is the reusable generic-open
perturbation bridge needed to descend from graph motions to body twists. -/
theorem exists_allCores_rigidityRank_eq_genericRigidityRank
    (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    ∃ p : BarJoint.Placement (H.BPVertex extra) 3,
      H.AllCoresAffinelyIndependent extra p ∧
      BarJoint.rigidityRank (H.bodyPinGraph extra) p =
        BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3 := by
  classical
  obtain ⟨p₀, hp₀⟩ := BarJoint.exists_rigidityRank_eq_genericRigidityRank
    (H.bodyPinGraph extra) 3
  let q := H.rigidTwistExtensionPlacement extra (fun _ ↦ 0)
  let U : Set (BarJoint.Placement (H.BPVertex extra) 3) :=
    {p | BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3 ≤
      BarJoint.rigidityRank (H.bodyPinGraph extra) p}
  have hU : IsOpen U := by
    exact BarJoint.isOpen_setOf_le_rigidityRank (H.bodyPinGraph extra)
      (BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3)
  have hpU : p₀ ∈ U := by
    change BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3 ≤
      BarJoint.rigidityRank (H.bodyPinGraph extra) p₀
    omega
  have hq : H.AllCoresAffinelyIndependent extra q := by
    exact H.rigidTwistExtensionPlacement_allCores extra (fun _ ↦ 0)
  obtain ⟨p, hpU', hpcores⟩ :=
    H.exists_mem_open_allCoresAffinelyIndependent extra p₀ q hq U hU hpU
  refine ⟨p, hpcores, Nat.le_antisymm ?_ hpU'⟩
  exact BarJoint.rigidityRank_le_genericRigidityRank
    (H.bodyPinGraph extra) 3 p

/-- At one placement, equality of graph and complete-graph ranks upgrades the
obvious reverse kernel inclusion to equality. -/
theorem rigidityOperator_ker_eq_complete_of_rank_eq
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hRank : BarJoint.rigidityRank (H.bodyPinGraph extra) p =
      BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra)) p) :
    (BarJoint.rigidityOperator (H.bodyPinGraph extra) p).ker =
      (BarJoint.rigidityOperator
        (SimpleGraph.completeGraph (H.BPVertex extra)) p).ker := by
  have hGraphLe : H.bodyPinGraph extra ≤
      SimpleGraph.completeGraph (H.BPVertex extra) := by
    rw [SimpleGraph.completeGraph_eq_top]
    exact le_top
  have hkerLe :
      (BarJoint.rigidityOperator
        (SimpleGraph.completeGraph (H.BPVertex extra)) p).ker ≤
      (BarJoint.rigidityOperator (H.bodyPinGraph extra) p).ker := by
    intro u hu
    exact infinitesimalMotion_of_le hGraphLe p u hu
  have hG := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator (H.bodyPinGraph extra) p)
  have hK := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator
      (SimpleGraph.completeGraph (H.BPVertex extra)) p)
  unfold BarJoint.rigidityRank at hRank
  have hkerFinrank : Module.finrank ℝ
      (BarJoint.rigidityOperator
        (SimpleGraph.completeGraph (H.BPVertex extra)) p).ker =
      Module.finrank ℝ
        (BarJoint.rigidityOperator (H.bodyPinGraph extra) p).ker := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hkerLe hkerFinrank).symm

/-- A complete framework containing one affine-independent labelled
tetrahedron has only global Euclidean infinitesimal motions. -/
theorem completeMotion_isGlobal_of_core
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) (b : H.Body)
    (hcore : H.CoreAffinelyIndependentAt extra p b)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hu : BarJoint.IsInfinitesimalMotion
      (SimpleGraph.completeGraph (H.BPVertex extra)) p u) :
    H.IsGlobalEuclideanMotion extra p u := by
  have hGraph : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u := by
    apply infinitesimalMotion_of_le (u := u) (p := p) ?_ hu
    rw [SimpleGraph.completeGraph_eq_top]
    exact le_top
  obtain ⟨Y, hY, _⟩ := exists_unique_twist_of_tetrahedronMotion
    (H.coreCoordinates extra p b) (H.coreVelocities extra u b) hcore
    (H.core_isTetrahedronInfinitesimalMotion_of_barMotion extra p u hGraph b)
  refine ⟨Y, ?_⟩
  funext v
  by_cases hvcore : ∃ i : Fin 4, v = H.privateCoreVertex extra b i
  · obtain ⟨i, rfl⟩ := hvcore
    simpa [coreVelocities, coreCoordinates] using hY i
  · apply sub_eq_zero.mp
    apply eq_zero_of_dot_sub_eq_zero_on_affineIndependent_four
      (H.coreCoordinates extra p b) hcore (p v)
      (u v - Twist.eval Y (p v))
    intro i
    have hne : v ≠ H.privateCoreVertex extra b i := by
      intro h
      exact hvcore ⟨i, h⟩
    have hadj : (SimpleGraph.completeGraph (H.BPVertex extra)).Adj v
        (H.privateCoreVertex extra b i) := by
      simpa using hne
    have hbar := (BarJoint.isInfinitesimalMotion_iff
      (SimpleGraph.completeGraph (H.BPVertex extra)) p u).mp hu
      v (H.privateCoreVertex extra b i) hadj
    have hfit := hY i
    change u (H.privateCoreVertex extra b i) =
      Twist.eval Y (p (H.privateCoreVertex extra b i)) at hfit
    simp only [BarJoint.edgeConstraint] at hbar
    rw [hfit] at hbar
    have htwist := twist_preserves_bar Y (p v)
      (p (H.privateCoreVertex extra b i))
    change Vec3.dot
      (p v - p (H.privateCoreVertex extra b i))
      (u v - Twist.eval Y (p v)) = 0
    simp only [Vec3.dot, Fin.sum_univ_three, Pi.sub_apply] at hbar htwist ⊢
    linear_combination hbar - htwist

/-- At a nondegenerate-core placement, equality with the complete-graph rank
forces the occurrence-level twist system itself to be rigid. -/
theorem twistRigidAt_pinCoordinates_of_rank_eq_complete
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) (b : H.Body)
    (hRank : BarJoint.rigidityRank (H.bodyPinGraph extra) p =
      BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra)) p) :
    TwistRigidAt H.left H.right (H.pinCoordinates extra p) := by
  intro X hX
  have huGraph : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p
      (H.twistVelocity extra p X) :=
    H.twistVelocity_isInfinitesimalMotion extra p X hX
  have hker := H.rigidityOperator_ker_eq_complete_of_rank_eq extra p hRank
  have huComplete : BarJoint.IsInfinitesimalMotion
      (SimpleGraph.completeGraph (H.BPVertex extra)) p
      (H.twistVelocity extra p X) := by
    change H.twistVelocity extra p X ∈
      (BarJoint.rigidityOperator
        (SimpleGraph.completeGraph (H.BPVertex extra)) p).ker
    rw [← hker]
    exact huGraph
  apply (H.diagonal_iff_twistVelocity_isGlobalEuclideanMotion_of_allCores
    extra p hcore X).2
  exact H.completeMotion_isGlobal_of_core extra p b (hcore b)
    (H.twistVelocity extra p X) huComplete

/-- For a nonempty body set, generic graph rigidity yields a nondegenerate
maximum-rank placement, hence a rigid occurrence-level twist realization and
therefore all partition inequalities. -/
theorem partitionCondition_of_genericallyRigidInR3_of_body
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (hRigid : H.GenericallyRigidInR3 extra) (b : H.Body) :
    H.PartitionCondition := by
  obtain ⟨p, hcore, hpmax⟩ :=
    H.exists_allCores_rigidityRank_eq_genericRigidityRank extra
  have hGraphLe : H.bodyPinGraph extra ≤
      SimpleGraph.completeGraph (H.BPVertex extra) := by
    rw [SimpleGraph.completeGraph_eq_top]
    exact le_top
  have hGeneric :
      BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3 =
        BarJoint.genericRigidityRank
          (SimpleGraph.completeGraph (H.BPVertex extra)) 3 := by
    exact hRigid
  have hRank : BarJoint.rigidityRank (H.bodyPinGraph extra) p =
      BarJoint.rigidityRank
        (SimpleGraph.completeGraph (H.BPVertex extra)) p := by
    apply Nat.le_antisymm
    · exact rigidityRank_mono hGraphLe p
    · calc
        BarJoint.rigidityRank
            (SimpleGraph.completeGraph (H.BPVertex extra)) p ≤
            BarJoint.genericRigidityRank
              (SimpleGraph.completeGraph (H.BPVertex extra)) 3 :=
          BarJoint.rigidityRank_le_genericRigidityRank _ 3 p
        _ = BarJoint.genericRigidityRank (H.bodyPinGraph extra) 3 :=
          hGeneric.symm
        _ = BarJoint.rigidityRank (H.bodyPinGraph extra) p := hpmax.symm
  have hTwist : TwistRigidAt H.left H.right (H.pinCoordinates extra p) :=
    H.twistRigidAt_pinCoordinates_of_rank_eq_complete extra p hcore b hRank
  exact H.partitionCondition_of_twistRigidAt (H.pinCoordinates extra p) hTwist

/-- On an empty body type every twist assignment is vacuously diagonal, so
the already-proved twist necessity theorem supplies the partition condition. -/
theorem partitionCondition_of_isEmptyBody
    (H : BodyPinIncidence) [IsEmpty H.Body] : H.PartitionCondition := by
  let pins : H.Pin → Vec3 ℝ := fun _ ↦ 0
  have hTwist : TwistRigidAt H.left H.right pins := by
    intro X hX
    refine ⟨0, ?_⟩
    funext b
    exact isEmptyElim b
  exact H.partitionCondition_of_twistRigidAt pins hTwist

/-- The genuine graph-theoretic necessary direction of the body--pin target. -/
theorem partitionCondition_of_genericallyRigidInR3
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (hRigid : H.GenericallyRigidInR3 extra) : H.PartitionCondition := by
  classical
  by_cases hBody : Nonempty H.Body
  · exact H.partitionCondition_of_genericallyRigidInR3_of_body
      extra hRigid (Classical.choice hBody)
  · letI : IsEmpty H.Body := not_nonempty_iff.mp hBody
    exact H.partitionCondition_of_isEmptyBody

end BodyPinIncidence

end RB31E2E
