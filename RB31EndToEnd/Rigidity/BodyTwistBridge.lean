import RB31EndToEnd.Rigidity.BodyPinGraph
import RB31EndToEnd.Linear.TwistSystem
import RB31EndToEnd.Linear.PinFibres

/-!
# The body-twist to bar-joint bridge

This file relates the occurrence-level twist system to the actual expanded
body--pin bar framework.  A pin vertex receives its velocity from the source
body; pin compatibility proves that the target body gives the same value.  No
rank formula or rigidity conclusion is built into the definitions.
-/

namespace RB31E2E

namespace BodyPinIncidence

/-- Extract the actual coordinates of the shared pin vertices. -/
def pinCoordinates (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) : H.Pin → Vec3 ℝ :=
  fun e ↦ p (H.pinVertex extra e)

/-- Extract the four distinguished private core coordinates of one body. -/
def coreCoordinates (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) (b : H.Body) : Fin 4 → Vec3 ℝ :=
  fun i ↦ p (H.privateCoreVertex extra b i)

/-- Restrict a graph velocity to the four private core vertices of one body. -/
def coreVelocities (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (u : BarJoint.Velocity (H.BPVertex extra) 3) (b : H.Body) : Fin 4 → Vec3 ℝ :=
  fun i ↦ u (H.privateCoreVertex extra b i)

/-- The four distinguished private vertices of body `b` form a tetrahedron. -/
def CoreAffinelyIndependentAt (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) (b : H.Body) : Prop :=
  AffineIndependent ℝ (H.coreCoordinates extra p b)

/-- Every body has an affinely independent private tetrahedral core. -/
def AllCoresAffinelyIndependent (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) : Prop :=
  ∀ b, H.CoreAffinelyIndependentAt extra p b

/-- A twist is determined by its values at four affinely independent points. -/
theorem twist_eq_of_eval_eq_on_affineIndependent_four
    (q : Fin 4 → Vec3 ℝ) (hq : AffineIndependent ℝ q)
    (X Y : Twist ℝ) (hXY : ∀ i, Twist.eval X (q i) = Twist.eval Y (q i)) :
    X = Y := by
  let Z : Twist ℝ := X - Y
  have hZeval (i : Fin 4) : Twist.eval Z (q i) = 0 := by
    dsimp [Z]
    rw [Twist.eval_sub]
    exact sub_eq_zero.mpr (hXY i)
  by_contra hne
  have hZne : Z ≠ 0 := by
    dsimp [Z]
    exact sub_ne_zero.mpr hne
  obtain ⟨c₁, c₂, hc₁, hc₂⟩ :=
    Twist.three_pin_solutions_collinear_of_ne_zero Z
      (q 0) (q 1) (q 2) hZne (hZeval 0) (hZeval 1) (hZeval 2)
  let f : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by omega)
  have hq₃ : AffineIndependent ℝ (q ∘ f) := hq.comp_embedding f
  have hNotCollinear : ¬ Collinear ℝ (Set.range (q ∘ f)) :=
    (affineIndependent_iff_not_collinear).mp hq₃
  apply hNotCollinear
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨q 0, Z.1, ?_⟩
  intro z hz
  rcases hz with ⟨i, rfl⟩
  fin_cases i
  · refine ⟨0, ?_⟩
    simp [f, Function.comp_apply]
  · refine ⟨c₁, ?_⟩
    simpa [f, Function.comp_apply] using (sub_eq_iff_eq_add.mp hc₁)
  · refine ⟨c₂, ?_⟩
    simpa [f, Function.comp_apply] using (sub_eq_iff_eq_add.mp hc₂)

/-- The six infinitesimal bar equations of a labelled tetrahedron. -/
def IsTetrahedronInfinitesimalMotion
    (q u : Fin 4 → Vec3 ℝ) : Prop :=
  ∀ i j, i ≠ j →
    ∑ c : Fin 3, (q i c - q j c) * (u i c - u j c) = 0

/-- Cross product by a fixed angular velocity, as a linear map. -/
def crossLinearMap (omega : Vec3 ℝ) : Vec3 ℝ →ₗ[ℝ] Vec3 ℝ where
  toFun x := Vec3.cross omega x
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Vec3.cross] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [Vec3.cross] <;> ring

@[simp] theorem crossLinearMap_apply (omega x : Vec3 ℝ) :
    crossLinearMap omega x = Vec3.cross omega x :=
  rfl

/-- The symmetric part of `x · A y`; it vanishes exactly when `A` is
skew-adjoint for the coordinate dot product. -/
noncomputable def skewBilinForm (A : Vec3 ℝ →ₗ[ℝ] Vec3 ℝ) :
    LinearMap.BilinForm ℝ (Vec3 ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y ↦ Vec3.dot x (A y) + Vec3.dot y (A x))
    (by
      intro x y z
      simp [Vec3.dot, Fin.sum_univ_three]
      ring)
    (by
      intro c x y
      simp [Vec3.dot, Fin.sum_univ_three]
      ring)
    (by
      intro x y z
      simp [Vec3.dot, Fin.sum_univ_three]
      ring)
    (by
      intro c x y
      simp [Vec3.dot, Fin.sum_univ_three]
      ring)

@[simp] theorem skewBilinForm_apply (A : Vec3 ℝ →ₗ[ℝ] Vec3 ℝ)
    (x y : Vec3 ℝ) :
    skewBilinForm A x y = Vec3.dot x (A y) + Vec3.dot y (A x) :=
  rfl

/-- Explicit finite-dimensional `K₄` infinitesimal rigidity: on an affinely
independent tetrahedron, every bar motion is induced by a unique twist. -/
theorem exists_unique_twist_of_tetrahedronMotion
    (q u : Fin 4 → Vec3 ℝ) (hq : AffineIndependent ℝ q)
    (hu : IsTetrahedronInfinitesimalMotion q u) :
    ∃! Y : Twist ℝ, ∀ i, u i = Twist.eval Y (q i) := by
  let aq : AffineBasis (Fin 4) ℝ (Vec3 ℝ) :=
    { toFun := q
      ind' := hq
      tot' := by
        apply (hq.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
        norm_num [Module.finrank_pi] }
  let bq := aq.basisOf (0 : Fin 4)
  let A : Vec3 ℝ →ₗ[ℝ] Vec3 ℝ :=
    (bq.constr ℝ) (fun j ↦ u j.1 - u 0)
  have hA (j : {j : Fin 4 // j ≠ 0}) :
      A (q j.1 - q 0) = u j.1 - u 0 := by
    have h := Module.Basis.constr_basis bq ℝ
      (fun j : {j : Fin 4 // j ≠ 0} ↦ u j.1 - u 0) j
    simpa [A, bq, aq] using h
  have hSbasis (j k : {j : Fin 4 // j ≠ 0}) :
      skewBilinForm A (bq j) (bq k) = 0 := by
    rw [skewBilinForm_apply]
    simp only [bq, AffineBasis.basisOf_apply]
    change Vec3.dot (q j.1 - q 0) (A (q k.1 - q 0)) +
      Vec3.dot (q k.1 - q 0) (A (q j.1 - q 0)) = 0
    rw [hA j, hA k]
    have hj₀ := hu j.1 0 j.2
    have hk₀ := hu k.1 0 k.2
    by_cases hjk : j.1 = k.1
    · have hjkSub : j = k := Subtype.ext hjk
      subst k
      simp only [Vec3.dot, Fin.sum_univ_three, Pi.sub_apply] at hj₀ ⊢
      linear_combination 2 * hj₀
    · have hjk' := hu j.1 k.1 hjk
      simp only [Vec3.dot, Fin.sum_univ_three, Pi.sub_apply] at hj₀ hk₀ hjk' ⊢
      linear_combination hj₀ + hk₀ - hjk'
  have hS : skewBilinForm A = 0 := by
    apply LinearMap.BilinForm.ext_basis bq
    intro j k
    simpa using hSbasis j k
  have hskew (x y : Vec3 ℝ) :
      Vec3.dot x (A y) + Vec3.dot y (A x) = 0 := by
    have hAt := congrArg
      (fun B : LinearMap.BilinForm ℝ (Vec3 ℝ) ↦ B x y) hS
    simpa using hAt
  let e := Pi.basisFun ℝ (Fin 3)
  let omega : Vec3 ℝ :=
    ![(A (e 1)) 2, (A (e 2)) 0, (A (e 0)) 1]
  have hAcross : A = crossLinearMap omega := by
    apply e.ext
    intro j
    funext i
    have h₀₀ := hskew (e 0) (e 0)
    have h₁₁ := hskew (e 1) (e 1)
    have h₂₂ := hskew (e 2) (e 2)
    have h₀₁ := hskew (e 0) (e 1)
    have h₀₂ := hskew (e 0) (e 2)
    have h₁₂ := hskew (e 1) (e 2)
    fin_cases j <;> fin_cases i <;>
      simp [e, Pi.basisFun_apply, Pi.single_apply, Vec3.dot,
        crossLinearMap, Vec3.cross, omega] at h₀₀ h₁₁ h₂₂ h₀₁ h₀₂ h₁₂ ⊢ <;>
      linarith
  let Y : Twist ℝ := (omega, u 0 - Vec3.cross omega (q 0))
  have hY (i : Fin 4) : u i = Twist.eval Y (q i) := by
    by_cases hi : i = 0
    · subst i
      simp [Y, Twist.eval]
    · let j : {j : Fin 4 // j ≠ 0} := ⟨i, hi⟩
      have hAi := hA j
      have hcross : Vec3.cross omega (q i - q 0) = u i - u 0 := by
        rw [← crossLinearMap_apply, ← hAcross]
        exact hAi
      funext c
      have hc := congrFun hcross c
      simp [Y, Twist.eval, Vec3.cross_sub_right] at hc ⊢
      linarith
  refine ⟨Y, hY, ?_⟩
  intro Z hZ
  apply twist_eq_of_eval_eq_on_affineIndependent_four q hq
  intro i
  exact (hZ i).symm.trans (hY i)

/-- Dot product against a fixed right-hand vector, as a linear functional. -/
noncomputable def dotRightLinearMap (d : Vec3 ℝ) : Vec3 ℝ →ₗ[ℝ] ℝ where
  toFun x := Vec3.dot x d
  map_add' x y := by
    simp [Vec3.dot, Fin.sum_univ_three]
    ring
  map_smul' c x := by
    simp [Vec3.dot, Fin.sum_univ_three]
    ring

@[simp] theorem dotRightLinearMap_apply (d x : Vec3 ℝ) :
    dotRightLinearMap d x = Vec3.dot x d :=
  rfl

/-- Four affine-independent displacement rows separate every velocity vector. -/
theorem eq_zero_of_dot_sub_eq_zero_on_affineIndependent_four
    (q : Fin 4 → Vec3 ℝ) (hq : AffineIndependent ℝ q)
    (x d : Vec3 ℝ) (horth : ∀ i, Vec3.dot (x - q i) d = 0) :
    d = 0 := by
  let aq : AffineBasis (Fin 4) ℝ (Vec3 ℝ) :=
    { toFun := q
      ind' := hq
      tot' := by
        apply (hq.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
        norm_num [Module.finrank_pi] }
  let bq := aq.basisOf (0 : Fin 4)
  have hb (j : {j : Fin 4 // j ≠ 0}) :
      Vec3.dot (bq j) d = 0 := by
    simp only [bq, AffineBasis.basisOf_apply]
    change Vec3.dot (q j.1 - q 0) d = 0
    have h₀ := horth 0
    have hj := horth j.1
    simp only [Vec3.dot, Fin.sum_univ_three, Pi.sub_apply] at h₀ hj ⊢
    linear_combination h₀ - hj
  have hfun : dotRightLinearMap d = 0 := by
    apply bq.ext
    intro j
    simpa using hb j
  have hdd : Vec3.dot d d = 0 := by
    have hAt := congrArg (fun f : Vec3 ℝ →ₗ[ℝ] ℝ ↦ f d) hfun
    simpa using hAt
  funext i
  have hsq₀ : 0 ≤ d 0 ^ 2 := sq_nonneg (d 0)
  have hsq₁ : 0 ≤ d 1 ^ 2 := sq_nonneg (d 1)
  have hsq₂ : 0 ≤ d 2 ^ 2 := sq_nonneg (d 2)
  fin_cases i <;>
    simp [Vec3.dot, Fin.sum_univ_three] at hdd ⊢ <;>
    nlinarith

/--
Velocity on every expanded graph vertex induced by body twists.  At a shared
pin occurrence we make the deterministic source-body choice; compatibility is
used below to recover the target-body value.
-/
def twistVelocity (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) (X : H.Body → Twist ℝ) :
    BarJoint.Velocity (H.BPVertex extra) 3
  | Sum.inl e => Twist.eval (X (H.left e)) (p (Sum.inl e))
  | Sum.inr x => Twist.eval (X x.1) (p (Sum.inr x))

@[simp] theorem twistVelocity_pin_source (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ) (e : H.Pin) :
    H.twistVelocity extra p X (H.pinVertex extra e) =
      Twist.eval (X (H.left e)) (H.pinCoordinates extra p e) :=
  rfl

@[simp] theorem twistVelocity_private (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ) (b : H.Body) (i : Fin (4 + extra b)) :
    H.twistVelocity extra p X (H.privateVertex extra b i) =
      Twist.eval (X b) (p (H.privateVertex extra b i)) :=
  rfl

/-- Affinely independent private cores make the twist-to-velocity map injective. -/
theorem twistVelocity_injective_of_allCoresAffinelyIndependent
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) :
    Function.Injective (H.twistVelocity extra p) := by
  intro X Y hvel
  funext b
  apply twist_eq_of_eval_eq_on_affineIndependent_four
    (H.coreCoordinates extra p b) (hcore b)
  intro i
  have hAt := congrFun hvel (H.privateCoreVertex extra b i)
  simpa [coreCoordinates, privateCoreVertex] using hAt

theorem twistVelocity_pin_target_of_compatible (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ)
    (hX : IsTwistMotion H.left H.right (H.pinCoordinates extra p) X)
    (e : H.Pin) :
    H.twistVelocity extra p X (H.pinVertex extra e) =
      Twist.eval (X (H.right e)) (H.pinCoordinates extra p e) := by
  exact hX e

/-- Compatibility makes the source-defined velocity equal to the twist of any
body to which the graph vertex belongs. -/
theorem twistVelocity_eq_eval_of_belongs (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ)
    (hX : IsTwistMotion H.left H.right (H.pinCoordinates extra p) X)
    (b : H.Body) (v : H.BPVertex extra)
    (hv : H.VertexBelongsToBody extra b v) :
    H.twistVelocity extra p X v = Twist.eval (X b) (p v) := by
  cases v with
  | inl e =>
      change H.left e = b ∨ H.right e = b at hv
      rcases hv with hb | hb
      · subst b
        rfl
      · simpa [pinCoordinates, pinVertex, hb] using
          H.twistVelocity_pin_target_of_compatible extra p X hX e
  | inr x =>
      rcases x with ⟨c, i⟩
      change c = b at hv
      subst b
      rfl

/-- A single Euclidean twist preserves the infinitesimal length of every pair. -/
theorem twist_preserves_bar (Y : Twist ℝ) (x y : Vec3 ℝ) :
    ∑ i : Fin 3, (x i - y i) * (Twist.eval Y x i - Twist.eval Y y i) = 0 := by
  simp [Twist.eval, Vec3.cross, Fin.sum_univ_succ]
  ring

/-- Every compatible body-twist motion induces a genuine bar-joint motion. -/
theorem twistVelocity_isInfinitesimalMotion (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ)
    (hX : IsTwistMotion H.left H.right (H.pinCoordinates extra p) X) :
    BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p
      (H.twistVelocity extra p X) := by
  rw [BarJoint.isInfinitesimalMotion_iff]
  intro v w hvw
  obtain ⟨b, _, hv, hw⟩ := (H.bodyPinGraph_adj_iff extra v w).mp hvw
  simp only [BarJoint.edgeConstraint]
  rw [H.twistVelocity_eq_eval_of_belongs extra p X hX b v hv,
    H.twistVelocity_eq_eval_of_belongs extra p X hX b w hw]
  exact twist_preserves_bar (X b) (p v) (p w)

/-- The actual solution type of the occurrence-level body-twist constraints. -/
def CompatibleTwistMotions (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) :=
  {X : H.Body → Twist ℝ //
    IsTwistMotion H.left H.right (H.pinCoordinates extra p) X}

/-- The actual kernel of the expanded bar-joint rigidity operator. -/
def ExpandedBarMotions (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) :=
  {u : BarJoint.Velocity (H.BPVertex extra) 3 //
    BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u}

theorem core_isTetrahedronInfinitesimalMotion_of_barMotion
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hu : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u)
    (b : H.Body) :
    IsTetrahedronInfinitesimalMotion
      (H.coreCoordinates extra p b) (H.coreVelocities extra u b) := by
  intro i j hij
  have hadj := H.privateCore_adj extra b hij
  have hbar := (BarJoint.isInfinitesimalMotion_iff
    (H.bodyPinGraph extra) p u).mp hu
    (H.privateCoreVertex extra b i) (H.privateCoreVertex extra b j) hadj
  simpa [BarJoint.edgeConstraint, coreCoordinates, coreVelocities] using hbar

/-- The forward kernel bridge from compatible body twists to graph motions. -/
def twistMotionToBarMotion (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3) :
    H.CompatibleTwistMotions extra p → H.ExpandedBarMotions extra p :=
  fun X ↦ ⟨H.twistVelocity extra p X.1,
    H.twistVelocity_isInfinitesimalMotion extra p X.1 X.2⟩

theorem twistMotionToBarMotion_injective_of_allCores
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) :
    Function.Injective (H.twistMotionToBarMotion extra p) := by
  intro X Y hXY
  apply Subtype.ext
  apply H.twistVelocity_injective_of_allCoresAffinelyIndependent extra p hcore
  exact congrArg Subtype.val hXY

/-- A graph velocity comes from one global Euclidean infinitesimal motion. -/
def IsGlobalEuclideanMotion (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3) : Prop :=
  ∃ Y : Twist ℝ, u = fun v ↦ Twist.eval Y (p v)

theorem globalEuclideanMotion_isInfinitesimalMotion (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hu : H.IsGlobalEuclideanMotion extra p u) :
    BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u := by
  rcases hu with ⟨Y, rfl⟩
  rw [BarJoint.isInfinitesimalMotion_iff]
  intro v w _
  exact twist_preserves_bar Y (p v) (p w)

/-- A diagonal body twist is exactly one global Euclidean motion on the graph. -/
theorem diagonal_twistVelocity_isGlobalEuclideanMotion (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ) (hX : IsDiagonalTwist X) :
    H.IsGlobalEuclideanMotion extra p (H.twistVelocity extra p X) := by
  rcases hX with ⟨Y, rfl⟩
  refine ⟨Y, ?_⟩
  funext v
  cases v <;> rfl

/-- On placements with nondegenerate cores, provenance is also reflected:
an induced velocity is global exactly when its body twists are diagonal. -/
theorem diagonal_iff_twistVelocity_isGlobalEuclideanMotion_of_allCores
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) (X : H.Body → Twist ℝ) :
    IsDiagonalTwist X ↔
      H.IsGlobalEuclideanMotion extra p (H.twistVelocity extra p X) := by
  constructor
  · exact H.diagonal_twistVelocity_isGlobalEuclideanMotion extra p X
  · rintro ⟨Y, hvel⟩
    refine ⟨Y, ?_⟩
    funext b
    apply twist_eq_of_eval_eq_on_affineIndependent_four
      (H.coreCoordinates extra p b) (hcore b)
    intro i
    have hAt := congrFun hvel (H.privateCoreVertex extra b i)
    simpa [coreCoordinates, privateCoreVertex] using hAt

theorem diagonal_twistVelocity_isInfinitesimalMotion (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (X : H.Body → Twist ℝ) (hX : IsDiagonalTwist X) :
    BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p
      (H.twistVelocity extra p X) :=
  H.globalEuclideanMotion_isInfinitesimalMotion extra p _
    (H.diagonal_twistVelocity_isGlobalEuclideanMotion extra p X hX)

/-- `u` is represented by the twist of every body on every vertex it owns. -/
def IsBodywiseTwistRepresentation (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3) (X : H.Body → Twist ℝ) : Prop :=
  ∀ b v, H.VertexBelongsToBody extra b v →
    u v = Twist.eval (X b) (p v)

/-- Provenance descent: a bodywise representation is automatically compatible
at every shared pin occurrence. -/
theorem isTwistMotion_of_bodywiseRepresentation (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3) (X : H.Body → Twist ℝ)
    (hrep : H.IsBodywiseTwistRepresentation extra p u X) :
    IsTwistMotion H.left H.right (H.pinCoordinates extra p) X := by
  intro e
  calc
    Twist.eval (X (H.left e)) (H.pinCoordinates extra p e) =
        u (H.pinVertex extra e) :=
      (hrep (H.left e) (H.pinVertex extra e) (by simp)).symm
    _ = Twist.eval (X (H.right e)) (H.pinCoordinates extra p e) :=
      hrep (H.right e) (H.pinVertex extra e) (by simp)

theorem velocity_eq_twistVelocity_of_bodywiseRepresentation
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3) (X : H.Body → Twist ℝ)
    (hrep : H.IsBodywiseTwistRepresentation extra p u X) :
    u = H.twistVelocity extra p X := by
  funext v
  cases v with
  | inl e =>
      exact hrep (H.left e) (H.pinVertex extra e) (by simp)
  | inr x =>
      rcases x with ⟨b, i⟩
      exact hrep b (H.privateVertex extra b i) (by simp)

/-- The inverse local bridge.  Its proof contains the finite-dimensional `K₄`
lemma above: no bodywise rigid-motion assertion is assumed as input. -/
theorem exists_bodywiseTwistRepresentation_of_infinitesimalMotion
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p)
    (hu : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u) :
    ∃ X : H.Body → Twist ℝ,
      H.IsBodywiseTwistRepresentation extra p u X := by
  classical
  have hex (b : H.Body) : ∃ Y : Twist ℝ, ∀ i,
      H.coreVelocities extra u b i =
        Twist.eval Y (H.coreCoordinates extra p b i) := by
    exact (exists_unique_twist_of_tetrahedronMotion
      (H.coreCoordinates extra p b) (H.coreVelocities extra u b)
      (hcore b)
      (H.core_isTetrahedronInfinitesimalMotion_of_barMotion extra p u hu b)).exists
  choose X hX using hex
  refine ⟨X, ?_⟩
  intro b v hv
  by_cases hvcore : ∃ i : Fin 4, v = H.privateCoreVertex extra b i
  · rcases hvcore with ⟨i, rfl⟩
    simpa [coreVelocities, coreCoordinates] using hX b i
  · apply sub_eq_zero.mp
    apply eq_zero_of_dot_sub_eq_zero_on_affineIndependent_four
      (H.coreCoordinates extra p b) (hcore b) (p v)
      (u v - Twist.eval (X b) (p v))
    intro i
    have hne : v ≠ H.privateCoreVertex extra b i := by
      intro h
      exact hvcore ⟨i, h⟩
    have hadj : (H.bodyPinGraph extra).Adj v
        (H.privateCoreVertex extra b i) := by
      rw [H.bodyPinGraph_adj_iff extra]
      exact ⟨b, hne, hv, H.privateCoreVertex_belongs extra b i⟩
    have hbar := (BarJoint.isInfinitesimalMotion_iff
      (H.bodyPinGraph extra) p u).mp hu
      v (H.privateCoreVertex extra b i) hadj
    have hfit := hX b i
    change u (H.privateCoreVertex extra b i) =
      Twist.eval (X b) (p (H.privateCoreVertex extra b i)) at hfit
    simp only [BarJoint.edgeConstraint] at hbar
    rw [hfit] at hbar
    have htwist := twist_preserves_bar (X b) (p v)
      (p (H.privateCoreVertex extra b i))
    change Vec3.dot
      (p v - p (H.privateCoreVertex extra b i))
      (u v - Twist.eval (X b) (p v)) = 0
    simp only [Vec3.dot, Fin.sum_univ_three,
      Pi.sub_apply] at hbar htwist ⊢
    linear_combination hbar - htwist

/-- Every graph motion on a nondegenerate expansion descends to a compatible
body-twist motion with exactly the same vertex velocity. -/
theorem exists_compatibleTwist_eq_of_infinitesimalMotion
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (u : BarJoint.Velocity (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p)
    (hu : BarJoint.IsInfinitesimalMotion (H.bodyPinGraph extra) p u) :
    ∃ X : H.Body → Twist ℝ,
      IsTwistMotion H.left H.right (H.pinCoordinates extra p) X ∧
      u = H.twistVelocity extra p X := by
  rcases H.exists_bodywiseTwistRepresentation_of_infinitesimalMotion
    extra p u hcore hu with ⟨X, hrep⟩
  exact ⟨X, H.isTwistMotion_of_bodywiseRepresentation extra p u X hrep,
    H.velocity_eq_twistVelocity_of_bodywiseRepresentation extra p u X hrep⟩

/-- Thus the forward kernel bridge is also surjective on nondegenerate cores. -/
theorem twistMotionToBarMotion_surjective_of_allCores
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) :
    Function.Surjective (H.twistMotionToBarMotion extra p) := by
  intro u
  rcases H.exists_compatibleTwist_eq_of_infinitesimalMotion
    extra p u.1 hcore u.2 with ⟨X, hX, huX⟩
  refine ⟨⟨X, hX⟩, ?_⟩
  apply Subtype.ext
  exact huX.symm

/-- Full pointwise kernel equivalence for every placement whose private cores
are affine-independent. -/
theorem twistMotionToBarMotion_bijective_of_allCores
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hcore : H.AllCoresAffinelyIndependent extra p) :
    Function.Bijective (H.twistMotionToBarMotion extra p) :=
  ⟨H.twistMotionToBarMotion_injective_of_allCores extra p hcore,
    H.twistMotionToBarMotion_surjective_of_allCores extra p hcore⟩

end BodyPinIncidence

end RB31E2E
