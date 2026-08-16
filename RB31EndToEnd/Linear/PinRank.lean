import RB31EndToEnd.Linear.PinFibres
import RB31EndToEnd.Specification

/-!
# Linear rank paid by one and two pins

This file proves the elementary `3,5,6` necessity bounds at the level
of one relative six-dimensional twist.
-/

namespace RB31E2E

namespace Twist

variable {k : Type*} [Field k]

/-- Evaluation at a pin is a linear map from twists to velocities. -/
def evalLinear (p : Vec3 k) : Twist k →ₗ[k] Vec3 k where
  toFun X := eval X p
  map_add' X Y := by
    change (X.2 + Y.2) + Vec3.cross (X.1 + Y.1) p =
      (X.2 + Vec3.cross X.1 p) + (Y.2 + Vec3.cross Y.1 p)
    rw [Vec3.cross_add_left]
    abel
  map_smul' a X := by
    change a • X.2 + Vec3.cross (a • X.1) p =
      a • (X.2 + Vec3.cross X.1 p)
    rw [Vec3.cross_smul_left, smul_add]

@[simp] theorem evalLinear_apply (p : Vec3 k) (X : Twist k) :
    evalLinear p X = eval X p := rfl

/-- Simultaneous evaluation at two pins. -/
def twoPinLinear (p q : Vec3 k) : Twist k →ₗ[k] (Vec3 k × Vec3 k) :=
  (evalLinear p).prod (evalLinear q)

@[simp] theorem twoPinLinear_apply (p q : Vec3 k) (X : Twist k) :
    twoPinLinear p q X = (eval X p, eval X q) := rfl

theorem finrank_vec3 : Module.finrank k (Vec3 k) = 3 := by
  simp [Vec3]

theorem finrank_twist : Module.finrank k (Twist k) = 6 := by
  simp [Twist, Vec3]

/-- One pin contributes at most three independent linear constraints. -/
theorem finrank_range_evalLinear_le_three (p : Vec3 k) :
    Module.finrank k (LinearMap.range (evalLinear p)) ≤ 3 := by
  calc
    Module.finrank k (LinearMap.range (evalLinear p)) ≤
        Module.finrank k (Vec3 k) := (LinearMap.range (evalLinear p)).finrank_le
    _ = 3 := finrank_vec3 (k := k)

private def e₀ : Vec3 k := fun i ↦ if i = 0 then 1 else 0

private theorem e₀_ne_zero : (e₀ : Vec3 k) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [e₀] at h0

/-- Two pin evaluations always have a nonzero relative rotation in their kernel. -/
theorem exists_ne_zero_mem_ker_twoPinLinear (p q : Vec3 k) :
    ∃ X : Twist k, X ≠ 0 ∧ X ∈ LinearMap.ker (twoPinLinear p q) := by
  by_cases hpq : p = q
  · subst q
    let X : Twist k := (e₀, -Vec3.cross e₀ p)
    refine ⟨X, ?_, ?_⟩
    · intro hX
      have hfst := congrArg Prod.fst hX
      exact e₀_ne_zero (by simpa [X] using hfst)
    · rw [LinearMap.mem_ker]
      apply Prod.ext <;> simp [X, eval]
  · let ω : Vec3 k := q - p
    let X : Twist k := (ω, -Vec3.cross ω p)
    have hω : ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    refine ⟨X, ?_, ?_⟩
    · intro hX
      have hfst := congrArg Prod.fst hX
      exact hω (by simpa [X] using hfst)
    · rw [LinearMap.mem_ker]
      apply Prod.ext
      · simp [X, eval]
      · change -Vec3.cross ω p + Vec3.cross ω q = 0
        rw [show -Vec3.cross ω p + Vec3.cross ω q =
          Vec3.cross ω q - Vec3.cross ω p by abel]
        rw [← Vec3.cross_sub_right]
        change Vec3.cross (q - p) (q - p) = 0
        exact Vec3.cross_self (q - p)

/-- Two pins contribute at most five independent linear constraints. -/
theorem finrank_range_twoPinLinear_le_five (p q : Vec3 k) :
    Module.finrank k (LinearMap.range (twoPinLinear p q)) ≤ 5 := by
  obtain ⟨X, hX, hXker⟩ := exists_ne_zero_mem_ker_twoPinLinear p q
  have hker : LinearMap.ker (twoPinLinear p q) ≠ ⊥ := by
    intro hk
    have : X = 0 := by
      have : X ∈ (⊥ : Submodule k (Twist k)) := hk ▸ hXker
      simpa using this
    exact hX this
  have hkerRank : 1 ≤ Module.finrank k (LinearMap.ker (twoPinLinear p q)) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hrankNullity := (twoPinLinear p q).finrank_range_add_finrank_ker
  rw [finrank_twist (k := k)] at hrankNullity
  omega

/-- Any linear family of constraints on one relative twist has rank at most six. -/
theorem finrank_range_le_six {M : Type*} [AddCommGroup M] [Module k M]
    (L : Twist k →ₗ[k] M) :
    Module.finrank k (LinearMap.range L) ≤ 6 := by
  calc
    Module.finrank k (LinearMap.range L) ≤ Module.finrank k (Twist k) :=
      LinearMap.finrank_range_le L
    _ = 6 := finrank_twist (k := k)

/-- Evaluation at every occurrence in one pin bundle. -/
noncomputable def bundleLinear {I : Type*} (p : I → Vec3 k) :
    Twist k →ₗ[k] (I → Vec3 k) :=
  LinearMap.pi fun i ↦ evalLinear (p i)

@[simp] theorem bundleLinear_apply {I : Type*} (p : I → Vec3 k)
    (X : Twist k) (i : I) :
    bundleLinear p X i = eval X (p i) := by
  simp [bundleLinear]

theorem finrank_bundleTarget (m : ℕ) :
    Module.finrank k (Fin m → Vec3 k) = m * 3 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_vec3 (k := k)]

private theorem exists_ne_zero_mem_ker_bundleLinear_two
    (p : Fin 2 → Vec3 k) :
    ∃ X : Twist k, X ≠ 0 ∧ X ∈ LinearMap.ker (bundleLinear p) := by
  obtain ⟨X, hX, hXker⟩ :=
    exists_ne_zero_mem_ker_twoPinLinear (p 0) (p 1)
  refine ⟨X, hX, ?_⟩
  rw [LinearMap.mem_ker]
  have hpair : twoPinLinear (p 0) (p 1) X = 0 :=
    LinearMap.mem_ker.mp hXker
  funext i
  fin_cases i
  · have h0 := congrArg Prod.fst hpair
    simpa using h0
  · have h1 := congrArg Prod.snd hpair
    simpa using h1

/--
The complete linear version of the `0,3,5,6` table: a bundle of `m`
pins imposes rank at most `pinCapacity m` on one relative twist.
-/
theorem finrank_range_bundleLinear_le_pinCapacity
    (m : ℕ) (p : Fin m → Vec3 k) :
    Module.finrank k (LinearMap.range (bundleLinear p)) ≤ pinCapacity m := by
  rcases m with _ | _ | _ | m
  · have h := (LinearMap.range (bundleLinear p)).finrank_le
    rw [finrank_bundleTarget] at h
    change Module.finrank k (LinearMap.range (bundleLinear p)) ≤ 0
    exact h
  · have h := (LinearMap.range (bundleLinear p)).finrank_le
    rw [finrank_bundleTarget] at h
    change Module.finrank k (LinearMap.range (bundleLinear p)) ≤ 3
    exact h
  · obtain ⟨X, hX, hXker⟩ := exists_ne_zero_mem_ker_bundleLinear_two p
    have hker : LinearMap.ker (bundleLinear p) ≠ ⊥ := by
      intro hk
      have : X = 0 := by
        have : X ∈ (⊥ : Submodule k (Twist k)) := hk ▸ hXker
        simpa using this
      exact hX this
    have hkerRank : 1 ≤ Module.finrank k (LinearMap.ker (bundleLinear p)) :=
      Submodule.one_le_finrank_iff.mpr hker
    have hrankNullity := (bundleLinear p).finrank_range_add_finrank_ker
    rw [finrank_twist (k := k)] at hrankNullity
    simp only [pinCapacity]
    omega
  · simpa [pinCapacity] using
      (finrank_range_le_six (k := k) (bundleLinear p))

end Twist

end RB31E2E
