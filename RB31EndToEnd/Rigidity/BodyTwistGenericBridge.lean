import RB31EndToEnd.Rigidity.BodyTwistBridge

/-!
# From one rigid twist realization to generic bar--joint rigidity

The argument uses no closed formula for the complete-graph rank.  We construct
one actual expanded placement, identify its graph-motion kernel with the
complete-graph kernel, and then connect this equality to the maximum-rank
semantics by finite-dimensional rank--nullity.
-/

namespace RB31E2E

namespace BodyPinIncidence

/-- The standard affine tetrahedron `0,e₀,e₁,e₂` in real three-space. -/
noncomputable def standardTetrahedronPoint : Fin 4 → Vec3 ℝ :=
  Fin.cases 0 (Pi.basisFun ℝ (Fin 3))

theorem standardTetrahedronPoint_affineIndependent :
    AffineIndependent ℝ standardTetrahedronPoint := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ standardTetrahedronPoint 0]
  apply (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 4))).mp
  simpa [standardTetrahedronPoint, Function.comp_apply, finSuccAboveEquiv_apply,
    Fin.succAbove_zero, Pi.basisFun_apply] using
    (Pi.basisFun ℝ (Fin 3)).linearIndependent

/-- Extend the standard four points to any larger private vertex set. -/
noncomputable def extendedTetrahedronPoint {n : ℕ} (i : Fin (4 + n)) : Vec3 ℝ :=
  if h : i.val < 4 then standardTetrahedronPoint ⟨i.val, h⟩ else 0

/--
An actual expanded placement with prescribed pin coordinates and a standard
private tetrahedron on every body.  Additional private vertices are placed at
the origin; their coordinates play no role in the kernel bridge.
-/
noncomputable def rigidTwistExtensionPlacement (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (pins : H.Pin → Vec3 ℝ) : BarJoint.Placement (H.BPVertex extra) 3
  | Sum.inl e => pins e
  | Sum.inr x => extendedTetrahedronPoint x.2

@[simp] theorem rigidTwistExtensionPlacement_pinCoordinates
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ) :
    H.pinCoordinates extra (H.rigidTwistExtensionPlacement extra pins) = pins := by
  funext e
  rfl

@[simp] theorem rigidTwistExtensionPlacement_coreCoordinates
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (b : H.Body) :
    H.coreCoordinates extra (H.rigidTwistExtensionPlacement extra pins) b =
      standardTetrahedronPoint := by
  funext i
  simp [coreCoordinates, rigidTwistExtensionPlacement, privateCoreVertex,
    privateVertex, extendedTetrahedronPoint]

theorem rigidTwistExtensionPlacement_allCores
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ) :
    H.AllCoresAffinelyIndependent extra
      (H.rigidTwistExtensionPlacement extra pins) := by
  intro b
  rw [CoreAffinelyIndependentAt,
    H.rigidTwistExtensionPlacement_coreCoordinates extra pins b]
  exact standardTetrahedronPoint_affineIndependent

/-- Infinitesimal-motion kernels are antitone under addition of bars. -/
theorem infinitesimalMotion_of_le {V : Type} {d : ℕ}
    {G K : SimpleGraph V} (hGK : G ≤ K)
    (p : BarJoint.Placement V d) (u : BarJoint.Velocity V d)
    (hu : BarJoint.IsInfinitesimalMotion K p u) :
    BarJoint.IsInfinitesimalMotion G p u := by
  rw [BarJoint.isInfinitesimalMotion_iff] at hu ⊢
  intro v w hvw
  exact hu v w (hGK hvw)

theorem rigidityRank_mono {V : Type} [Fintype V] {d : ℕ}
    {G K : SimpleGraph V} (hGK : G ≤ K) (p : BarJoint.Placement V d) :
    BarJoint.rigidityRank G p ≤ BarJoint.rigidityRank K p := by
  have hker : (BarJoint.rigidityOperator K p).ker ≤
      (BarJoint.rigidityOperator G p).ker := by
    intro u hu
    exact infinitesimalMotion_of_le hGK p u hu
  have hdim := Submodule.finrank_mono hker
  have hG := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator G p)
  have hK := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator K p)
  change Module.finrank ℝ (BarJoint.rigidityOperator G p).range ≤
    Module.finrank ℝ (BarJoint.rigidityOperator K p).range
  omega

theorem genericRigidityRank_mono {V : Type} [Fintype V] {d : ℕ}
    {G K : SimpleGraph V} (hGK : G ≤ K) :
    BarJoint.genericRigidityRank G d ≤ BarJoint.genericRigidityRank K d := by
  rcases BarJoint.exists_rigidityRank_eq_genericRigidityRank G d with ⟨p, hp⟩
  rw [← hp]
  exact (rigidityRank_mono hGK p).trans
    (BarJoint.rigidityRank_le_genericRigidityRank K d p)

/-- A global Euclidean velocity satisfies every edge of the complete graph. -/
theorem globalEuclideanMotion_isCompleteMotion {V : Type}
    (p : BarJoint.Placement V 3) (u : BarJoint.Velocity V 3)
    (hu : ∃ Y : Twist ℝ, u = fun v ↦ Twist.eval Y (p v)) :
    BarJoint.IsInfinitesimalMotion (SimpleGraph.completeGraph V) p u := by
  rcases hu with ⟨Y, rfl⟩
  rw [BarJoint.isInfinitesimalMotion_iff]
  intro v w _
  exact twist_preserves_bar Y (p v) (p w)

/-- Evaluation of one global twist on every vertex, as a linear map. -/
noncomputable def globalTwistEvaluation {V : Type}
    (p : BarJoint.Placement V 3) : Twist ℝ →ₗ[ℝ] BarJoint.Velocity V 3 where
  toFun Y := fun v ↦ Twist.eval Y (p v)
  map_add' X Y := by
    funext v i
    change (X.2 i + Y.2 i) + Vec3.cross (X.1 + Y.1) (p v) i =
      (X.2 i + Vec3.cross X.1 (p v) i) +
        (Y.2 i + Vec3.cross Y.1 (p v) i)
    fin_cases i <;> simp [Vec3.cross] <;> ring
  map_smul' c X := by
    funext v i
    change c * X.2 i + Vec3.cross (c • X.1) (p v) i =
      c * (X.2 i + Vec3.cross X.1 (p v) i)
    fin_cases i <;> simp [Vec3.cross] <;> ring

@[simp] theorem globalTwistEvaluation_apply {V : Type}
    (p : BarJoint.Placement V 3) (Y : Twist ℝ) (v : V) :
    globalTwistEvaluation p Y v = Twist.eval Y (p v) :=
  rfl

theorem globalTwistEvaluation_injective_of_affineIndependent_four
    {V : Type} (p : BarJoint.Placement V 3) (f : Fin 4 → V)
    (hf : AffineIndependent ℝ (p ∘ f)) :
    Function.Injective (globalTwistEvaluation p) := by
  intro X Y hXY
  apply twist_eq_of_eval_eq_on_affineIndependent_four (p ∘ f) hf
  intro i
  have hAt := congrFun hXY (f i)
  simpa [Function.comp_apply] using hAt

theorem dotRightLinearMap_surjective_of_ne_zero
    (d : Vec3 ℝ) (hd : d ≠ 0) :
    Function.Surjective (dotRightLinearMap d) := by
  have hcoord : ∃ i : Fin 3, d i ≠ 0 := by
    by_contra h
    apply hd
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hcoord with ⟨i, hi⟩
  intro r
  fin_cases i
  · refine ⟨![r / d 0, 0, 0], ?_⟩
    change d 0 ≠ 0 at hi
    simp [dotRightLinearMap, Vec3.dot, Fin.sum_univ_three]
    exact div_mul_cancel₀ r hi
  · refine ⟨![0, r / d 1, 0], ?_⟩
    change d 1 ≠ 0 at hi
    simp [dotRightLinearMap, Vec3.dot, Fin.sum_univ_three]
    exact div_mul_cancel₀ r hi
  · refine ⟨![0, 0, r / d 2], ?_⟩
    change d 2 ≠ 0 at hi
    simp [dotRightLinearMap, Vec3.dot, Fin.sum_univ_three]
    exact div_mul_cancel₀ r hi

theorem dotRightLinearMap_ker_finrank_of_ne_zero
    (d : Vec3 ℝ) (hd : d ≠ 0) :
    Module.finrank ℝ (dotRightLinearMap d).ker = 2 := by
  have hsurj := dotRightLinearMap_surjective_of_ne_zero d hd
  have hRN := LinearMap.finrank_range_add_finrank_ker (dotRightLinearMap d)
  have hrange : (dotRightLinearMap d).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange] at hRN
  norm_num [Module.finrank_pi] at hRN ⊢
  omega

/-- Every complete framework on at least four labelled vertices has motion
kernel dimension at least six.  In the degenerate case the proof constructs a
large subspace of velocities normal to the common stationary-twist axis. -/
theorem six_le_complete_ker_finrank {V : Type} [Fintype V]
    (hcard : 4 ≤ Fintype.card V) (p : BarJoint.Placement V 3) :
    6 ≤ Module.finrank ℝ
      (BarJoint.rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  classical
  let E := globalTwistEvaluation p
  by_cases hEinj : Function.Injective E
  · let F : Twist ℝ →ₗ[ℝ]
        (BarJoint.rigidityOperator (SimpleGraph.completeGraph V) p).ker :=
      LinearMap.codRestrict _ E (by
        intro Y
        exact globalEuclideanMotion_isCompleteMotion p (E Y) ⟨Y, rfl⟩)
    have hFin := LinearMap.finrank_le_finrank_of_injective (f := F) (by
      intro X Y hXY
      apply hEinj
      exact congrArg Subtype.val hXY)
    have hTwist : Module.finrank ℝ (Twist ℝ) = 6 := by
      norm_num [Module.finrank_prod, Module.finrank_pi]
    simpa [hTwist] using hFin
  · have hEker : E.ker ≠ ⊥ := by
      intro hbot
      exact hEinj (LinearMap.ker_eq_bot.mp hbot)
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hEker with ⟨Z, hZker, hZne⟩
    have hEvalZero : E Z = 0 := LinearMap.mem_ker.mp hZker
    have hcardPos : 0 < Fintype.card V := by omega
    let v₀ : V := Classical.choice (Fintype.card_pos_iff.mp hcardPos)
    have hZeval (v : V) : Twist.eval Z (p v) = 0 := by
      have hAt := congrFun hEvalZero v
      simpa [E] using hAt
    have hAngular : Z.1 ≠ 0 :=
      Twist.angular_ne_zero_of_ne_zero_of_eval_eq_zero Z (p v₀) hZne (hZeval v₀)
    have hline (v : V) : ∃ c : ℝ, p v - p v₀ = c • Z.1 :=
      Twist.pin_sub_eq_smul_angular Z (p v₀) (p v) hAngular
        (hZeval v₀) (hZeval v)
    choose c hc using hline
    let N := (dotRightLinearMap Z.1).ker
    let inclusion : (V → N) →ₗ[ℝ] BarJoint.Velocity V 3 :=
      { toFun := fun u v ↦ (u v).1
        map_add' := by
          intro u w
          funext v i
          rfl
        map_smul' := by
          intro a u
          funext v i
          rfl }
    have hinclusionMotion (u : V → N) :
        BarJoint.IsInfinitesimalMotion (SimpleGraph.completeGraph V) p
          (inclusion u) := by
      rw [BarJoint.isInfinitesimalMotion_iff]
      intro v w _
      have hdiff : p v - p w = (c v - c w) • Z.1 := by
        calc
          p v - p w = (p v - p v₀) - (p w - p v₀) := by abel
          _ = c v • Z.1 - c w • Z.1 := by rw [hc v, hc w]
          _ = (c v - c w) • Z.1 := by
            funext i
            simp
            ring
      have hvorth : Vec3.dot (u v).1 Z.1 = 0 := by
        exact LinearMap.mem_ker.mp (u v).2
      have hworth : Vec3.dot (u w).1 Z.1 = 0 := by
        exact LinearMap.mem_ker.mp (u w).2
      simp only [BarJoint.edgeConstraint]
      change ∑ i : Fin 3,
        (p v - p w) i * ((u v).1 i - (u w).1 i) = 0
      rw [hdiff]
      simp only [Pi.smul_apply, smul_eq_mul, Vec3.dot,
        Fin.sum_univ_three] at hvorth hworth ⊢
      linear_combination (c v - c w) * (hvorth - hworth)
    let F : (V → N) →ₗ[ℝ]
        (BarJoint.rigidityOperator (SimpleGraph.completeGraph V) p).ker :=
      LinearMap.codRestrict _ inclusion hinclusionMotion
    have hFin := LinearMap.finrank_le_finrank_of_injective (f := F) (by
      intro u w huw
      funext v
      apply Subtype.ext
      have hval := congrArg Subtype.val huw
      exact congrFun hval v)
    have hN : Module.finrank ℝ N = 2 :=
      dotRightLinearMap_ker_finrank_of_ne_zero Z.1 hAngular
    have hDomain : Module.finrank ℝ (V → N) = Fintype.card V * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [hN]
    rw [hDomain] at hFin
    omega

/-- At the constructed placement, twist rigidity forces every expanded graph
motion to be one global Euclidean motion. -/
theorem every_barMotion_global_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hu : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra)
      (H.rigidTwistExtensionPlacement extra pins) u) :
    H.IsGlobalEuclideanMotion extra
      (H.rigidTwistExtensionPlacement extra pins) u := by
  let p := H.rigidTwistExtensionPlacement extra pins
  have hcore : H.AllCoresAffinelyIndependent extra p :=
    H.rigidTwistExtensionPlacement_allCores extra pins
  rcases H.exists_compatibleTwist_eq_of_infinitesimalMotion
    extra p u hcore hu with ⟨X, hX, huX⟩
  have hdiag : IsDiagonalTwist X := by
    apply hRigid X
    simpa [p] using hX
  rw [huX]
  exact H.diagonal_twistVelocity_isGlobalEuclideanMotion extra p X hdiag

/-- The graph and complete graph have exactly the same kernel at the
constructed placement. -/
theorem rigidityOperator_ker_eq_complete_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) :
    (BarJoint.rigidityOperator (H.bodyPinGraph extra)
      (H.rigidTwistExtensionPlacement extra pins)).ker =
    (BarJoint.rigidityOperator
      (SimpleGraph.completeGraph (H.BPVertex extra))
      (H.rigidTwistExtensionPlacement extra pins)).ker := by
  ext u
  change BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra)
      (H.rigidTwistExtensionPlacement extra pins) u ↔
    BarJoint.IsInfinitesimalMotion (SimpleGraph.completeGraph (H.BPVertex extra))
      (H.rigidTwistExtensionPlacement extra pins) u
  constructor
  · intro hu
    exact globalEuclideanMotion_isCompleteMotion _ u
      (H.every_barMotion_global_of_twistRigidAt extra pins hRigid u hu)
  · intro hu
    apply infinitesimalMotion_of_le (p := H.rigidTwistExtensionPlacement extra pins)
      (u := u) ?_ hu
    rw [SimpleGraph.completeGraph_eq_top]
    exact le_top

theorem complete_ker_eq_globalTwist_range_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) :
    (BarJoint.rigidityOperator
      (SimpleGraph.completeGraph (H.BPVertex extra))
      (H.rigidTwistExtensionPlacement extra pins)).ker =
    (globalTwistEvaluation
      (H.rigidTwistExtensionPlacement extra pins)).range := by
  ext u
  constructor
  · intro hu
    have huComplete : BarJoint.IsInfinitesimalMotion
        (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins) u := hu
    have huGraph : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra)
        (H.rigidTwistExtensionPlacement extra pins) u := by
      apply infinitesimalMotion_of_le (p := H.rigidTwistExtensionPlacement extra pins)
        (u := u) ?_ huComplete
      rw [SimpleGraph.completeGraph_eq_top]
      exact le_top
    rcases H.every_barMotion_global_of_twistRigidAt extra pins hRigid u huGraph with
      ⟨Y, hY⟩
    exact LinearMap.mem_range.mpr ⟨Y, hY.symm⟩
  · intro hu
    rcases LinearMap.mem_range.mp hu with ⟨Y, rfl⟩
    exact globalEuclideanMotion_isCompleteMotion _ _ ⟨Y, rfl⟩

/-- With one body present, the constructed complete framework has a
six-dimensional kernel, proved from the explicit tetrahedral core. -/
theorem complete_ker_finrank_eq_six_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) (b : H.Body) :
    Module.finrank ℝ
      (BarJoint.rigidityOperator
        (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins)).ker = 6 := by
  let p := H.rigidTwistExtensionPlacement extra pins
  have hinj : Function.Injective (globalTwistEvaluation p) := by
    apply globalTwistEvaluation_injective_of_affineIndependent_four p
      (H.privateCoreVertex extra b)
    simpa [p, Function.comp_apply, coreCoordinates] using
      (H.rigidTwistExtensionPlacement_allCores extra pins b)
  have hRN := LinearMap.finrank_range_add_finrank_ker
    (globalTwistEvaluation p)
  have hker : (globalTwistEvaluation p).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  rw [hker] at hRN
  have hTwist : Module.finrank ℝ (Twist ℝ) = 6 := by
    norm_num [Module.finrank_prod, Module.finrank_pi]
  rw [H.complete_ker_eq_globalTwist_range_of_twistRigidAt extra pins hRigid]
  simpa [hTwist] using hRN

theorem complete_rigidityRank_le_constructed_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) (b : H.Body)
    (q : BarJoint.Placement (H.BPVertex extra) 3) :
    BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra)) q ≤
      BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins) := by
  have hcard : 4 ≤ Fintype.card (H.BPVertex extra) := by
    simpa using Fintype.card_le_of_injective
      (H.privateCoreVertex extra b) (H.privateCoreVertex_injective extra b)
  have hkerQ := six_le_complete_ker_finrank hcard q
  have hkerP := H.complete_ker_finrank_eq_six_of_twistRigidAt
    extra pins hRigid b
  have hQ := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator (SimpleGraph.completeGraph (H.BPVertex extra)) q)
  have hP := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator (SimpleGraph.completeGraph (H.BPVertex extra))
      (H.rigidTwistExtensionPlacement extra pins))
  change Module.finrank ℝ
      (BarJoint.rigidityOperator (SimpleGraph.completeGraph (H.BPVertex extra)) q).range ≤
    Module.finrank ℝ
      (BarJoint.rigidityOperator (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins)).range
  omega

/-- The constructed complete placement attains the maximum complete-graph
rank; no numerical complete-rank formula is used. -/
theorem complete_genericRank_eq_constructed_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) (b : H.Body) :
    BarJoint.genericRigidityRank (SimpleGraph.completeGraph (H.BPVertex extra)) 3 =
      BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins) := by
  apply Nat.le_antisymm
  · rcases BarJoint.exists_rigidityRank_eq_genericRigidityRank
      (SimpleGraph.completeGraph (H.BPVertex extra)) 3 with ⟨q, hq⟩
    rw [← hq]
    exact H.complete_rigidityRank_le_constructed_of_twistRigidAt
      extra pins hRigid b q
  · exact BarJoint.rigidityRank_le_genericRigidityRank
      (SimpleGraph.completeGraph (H.BPVertex extra)) 3
      (H.rigidTwistExtensionPlacement extra pins)

theorem rigidityRank_eq_complete_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) :
    BarJoint.rigidityRank (H.bodyPinGraph extra)
        (H.rigidTwistExtensionPlacement extra pins) =
      BarJoint.rigidityRank (SimpleGraph.completeGraph (H.BPVertex extra))
        (H.rigidTwistExtensionPlacement extra pins) := by
  have hker := H.rigidityOperator_ker_eq_complete_of_twistRigidAt
    extra pins hRigid
  have hG := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator (H.bodyPinGraph extra)
      (H.rigidTwistExtensionPlacement extra pins))
  have hK := LinearMap.finrank_range_add_finrank_ker
    (BarJoint.rigidityOperator (SimpleGraph.completeGraph (H.BPVertex extra))
      (H.rigidTwistExtensionPlacement extra pins))
  unfold BarJoint.rigidityRank
  rw [hker] at hG
  omega

theorem genericallyRigidInR3_of_twistRigidAt_of_body
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) (b : H.Body) :
    H.GenericallyRigidInR3 extra := by
  unfold GenericallyRigidInR3 BarJoint.IsGenericallyRigidInR3
    BarJoint.IsGenericallyRigidInDimension
  apply Nat.le_antisymm
  · apply genericRigidityRank_mono
    rw [SimpleGraph.completeGraph_eq_top]
    exact le_top
  · rw [H.complete_genericRank_eq_constructed_of_twistRigidAt
      extra pins hRigid b,
    ← H.rigidityRank_eq_complete_of_twistRigidAt extra pins hRigid]
    exact BarJoint.rigidityRank_le_genericRigidityRank
      (H.bodyPinGraph extra) 3 (H.rigidTwistExtensionPlacement extra pins)

/-- If there are no bodies, looplessness makes the pin and expanded vertex
types empty, so both the body--pin graph and complete graph are empty. -/
theorem genericallyRigidInR3_of_isEmptyBody
    (H : BodyPinIncidence) (extra : H.Body → ℕ) [IsEmpty H.Body] :
    H.GenericallyRigidInR3 extra := by
  letI : IsEmpty H.Pin := ⟨fun e ↦ isEmptyElim (H.left e)⟩
  letI : IsEmpty (H.BPVertex extra) := ⟨fun v ↦ by
    cases v with
    | inl e => exact isEmptyElim e
    | inr x => exact isEmptyElim x.1⟩
  letI : Subsingleton (H.BPVertex extra) := ⟨fun v _ ↦ isEmptyElim v⟩
  unfold GenericallyRigidInR3 BarJoint.IsGenericallyRigidInR3
    BarJoint.IsGenericallyRigidInDimension
  rw [BarJoint.eq_bot_of_subsingleton (H.bodyPinGraph extra),
    BarJoint.eq_bot_of_subsingleton
      (SimpleGraph.completeGraph (H.BPVertex extra))]

/-- Main sufficient generic bridge requested by the body--pin program. -/
theorem genericallyRigidInR3_of_twistRigidAt
    (H : BodyPinIncidence) (extra : H.Body → ℕ) (pins : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right pins) :
    H.GenericallyRigidInR3 extra := by
  classical
  by_cases hBody : Nonempty H.Body
  · exact H.genericallyRigidInR3_of_twistRigidAt_of_body
      extra pins hRigid (Classical.choice hBody)
  · letI : IsEmpty H.Body := not_nonempty_iff.mp hBody
    exact H.genericallyRigidInR3_of_isEmptyBody extra

theorem genericallyRigidInR3_of_hasRigidTwistRealization
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (hRigid : HasRigidTwistRealization (k := ℝ) H.left H.right) :
    H.GenericallyRigidInR3 extra := by
  rcases hRigid with ⟨pins, hpins⟩
  exact H.genericallyRigidInR3_of_twistRigidAt extra pins hpins

end BodyPinIncidence

end RB31E2E
