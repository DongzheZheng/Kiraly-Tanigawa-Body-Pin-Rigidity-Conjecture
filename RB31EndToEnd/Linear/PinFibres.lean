import RB31EndToEnd.Linear.Vec3Twist

/-!
# Elementary pin fibres

The zero set of the velocity of a nonzero twist is an affine line parallel to
its angular part.  Everything here is coordinate algebra over an arbitrary
field; no genericity, characteristic, or algebraic-geometry hypothesis is
used.
-/

namespace RB31E2E

namespace Vec3

/-- The cross product is additive in its second argument. -/
theorem cross_sub_right {k : Type*} [CommRing k] (x p q : Vec3 k) :
    cross x (p - q) = cross x p - cross x q := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

/-- Over a field, the kernel of `p ↦ ω × p` is the line spanned by a
nonzero vector `ω`. -/
theorem cross_eq_zero_iff_eq_smul {k : Type*} [Field k]
    (ω d : Vec3 k) (hω : ω ≠ 0) :
    cross ω d = 0 ↔ ∃ c : k, d = c • ω := by
  constructor
  · intro hcross
    have hc0 : ω 1 * d 2 - ω 2 * d 1 = 0 := by
      simpa [cross] using congrFun hcross (0 : Fin 3)
    have hc1 : ω 2 * d 0 - ω 0 * d 2 = 0 := by
      simpa [cross] using congrFun hcross (1 : Fin 3)
    have hc2 : ω 0 * d 1 - ω 1 * d 0 = 0 := by
      simpa [cross] using congrFun hcross (2 : Fin 3)
    have hcoord : ∃ i : Fin 3, ω i ≠ 0 := by
      by_contra h
      apply hω
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    fin_cases i
    · change ω 0 ≠ 0 at hi
      refine ⟨d 0 / ω 0, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 0 / ω 0 * ω 0
        exact (div_mul_cancel₀ (d 0) hi).symm
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 0 / ω 0 * ω 1
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc2
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 0 / ω 0 * ω 2
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc1
    · change ω 1 ≠ 0 at hi
      refine ⟨d 1 / ω 1, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 1 / ω 1 * ω 0
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc2
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 1 / ω 1 * ω 1
        exact (div_mul_cancel₀ (d 1) hi).symm
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 1 / ω 1 * ω 2
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc0
    · change ω 2 ≠ 0 at hi
      refine ⟨d 2 / ω 2, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 2 / ω 2 * ω 0
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc1
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 2 / ω 2 * ω 1
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc0
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 2 / ω 2 * ω 2
        exact (div_mul_cancel₀ (d 2) hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    fin_cases i <;> simp [cross] <;> ring

end Vec3

namespace Twist

/-- A pin solution puts its twist on the split--Klein quadric. -/
theorem splitKlein_eq_zero_of_pin_solution {k : Type*} [Field k]
    (X : Twist k) (p : Vec3 k) (hp : eval X p = 0) :
    splitKlein X = 0 :=
  splitKlein_eq_zero_of_eval_eq_zero X p hp

/-- A nonzero twist admitting a stationary pin has nonzero angular part. -/
theorem angular_ne_zero_of_ne_zero_of_eval_eq_zero {k : Type*} [Field k]
    (X : Twist k) (p : Vec3 k) (hX : X ≠ 0) (hp : eval X p = 0) :
    X.1 ≠ 0 := by
  intro hω
  have hcross : Vec3.cross X.1 p = 0 := by
    funext i
    fin_cases i <;> simp [Vec3.cross, hω]
  have hv : X.2 = 0 := by
    rw [eval, hcross, add_zero] at hp
    exact hp
  exact hX (Prod.ext hω hv)

/-- Two stationary pins of a twist differ in a direction killed by its
angular cross-product map. -/
theorem cross_pin_sub_eq_zero {k : Type*} [Field k]
    (X : Twist k) (p p' : Vec3 k)
    (hp : eval X p = 0) (hp' : eval X p' = 0) :
    Vec3.cross X.1 (p' - p) = 0 := by
  rw [Vec3.cross_sub_right]
  have hcross : Vec3.cross X.1 p' = Vec3.cross X.1 p := by
    apply add_left_cancel (a := X.2)
    exact hp'.trans hp.symm
  rw [hcross, sub_self]

/-- If the angular part is nonzero, any two stationary pins differ by a
scalar multiple of it. -/
theorem pin_sub_eq_smul_angular {k : Type*} [Field k]
    (X : Twist k) (p p' : Vec3 k) (hω : X.1 ≠ 0)
    (hp : eval X p = 0) (hp' : eval X p' = 0) :
    ∃ c : k, p' - p = c • X.1 :=
  (Vec3.cross_eq_zero_iff_eq_smul X.1 (p' - p) hω).mp
    (cross_pin_sub_eq_zero X p p' hp hp')

/-- Exact affine-collinearity statement for three stationary pins: both
differences from the first pin are scalar multiples of the angular part. -/
theorem three_pin_solutions_collinear {k : Type*} [Field k]
    (X : Twist k) (p₀ p₁ p₂ : Vec3 k) (hω : X.1 ≠ 0)
    (hp₀ : eval X p₀ = 0) (hp₁ : eval X p₁ = 0)
    (hp₂ : eval X p₂ = 0) :
    ∃ c₁ c₂ : k, p₁ - p₀ = c₁ • X.1 ∧ p₂ - p₀ = c₂ • X.1 := by
  obtain ⟨c₁, hc₁⟩ := pin_sub_eq_smul_angular X p₀ p₁ hω hp₀ hp₁
  obtain ⟨c₂, hc₂⟩ := pin_sub_eq_smul_angular X p₀ p₂ hω hp₀ hp₂
  exact ⟨c₁, c₂, hc₁, hc₂⟩

/-- A formulation needing only that the twist itself is nonzero: one pin
solution already forces the angular direction to be nonzero. -/
theorem three_pin_solutions_collinear_of_ne_zero {k : Type*} [Field k]
    (X : Twist k) (p₀ p₁ p₂ : Vec3 k) (hX : X ≠ 0)
    (hp₀ : eval X p₀ = 0) (hp₁ : eval X p₁ = 0)
    (hp₂ : eval X p₂ = 0) :
    ∃ c₁ c₂ : k, p₁ - p₀ = c₁ • X.1 ∧ p₂ - p₀ = c₂ • X.1 := by
  apply three_pin_solutions_collinear X p₀ p₁ p₂
    (angular_ne_zero_of_ne_zero_of_eval_eq_zero X p₀ hX hp₀)
    hp₀ hp₁ hp₂

end Twist

end RB31E2E
