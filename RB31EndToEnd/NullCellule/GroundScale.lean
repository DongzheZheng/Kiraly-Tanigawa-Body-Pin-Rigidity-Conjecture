import RB31EndToEnd.Algebra.GroundedTwist
import RB31EndToEnd.NullCellule.Definitions

/-!
# Grounding and the free common-scaling orbit

This file proves the point-set content of the one-dimensional orbit drop.
The later algebraic-geometric layer still has to convert this free orbit into
a dimension inequality; that conversion is deliberately not postulated here.
-/

namespace RB31E2E

variable {k V W E : Type*} [Field k]

/-- Scaling every twist by the same scalar preserves all pin equations. -/
theorem IsTwistMotion.smul {src dst : E → W} {p : E → Vec3 k}
    {X : W → Twist k} (hX : IsTwistMotion src dst p X) (a : k) :
    IsTwistMotion src dst p (fun w ↦ a • X w) := by
  intro e
  have he := congrArg (fun z : Vec3 k ↦ a • z) (hX e)
  simpa [Twist.eval, Vec3.cross_smul_left] using he

/-- A nonzero common scalar preserves and reflects equality of two labels. -/
theorem smul_twist_eq_smul_twist_iff {a : k} (ha : a ≠ 0)
    (X Y : Twist k) : a • X = a • Y ↔ X = Y := by
  constructor
  · intro hXY
    have hzero : a • (X - Y) = 0 := by
      rw [smul_sub, hXY, sub_self]
    have : X - Y = 0 := by
      rcases smul_eq_zero.mp hzero with h | h
      · exact (ha h).elim
      · exact h
    exact sub_eq_zero.mp this
  · rintro rfl
    rfl

/-- Hence a nonzero common scalar preserves the exact equality partition. -/
theorem commonScale_eq_iff {a : k} (ha : a ≠ 0) (X : V → Twist k) (u v : V) :
    a • X u = a • X v ↔ X u = X v :=
  smul_twist_eq_smul_twist_iff ha _ _

/-- Grounding is stable under common scaling. -/
theorem commonScale_grounded {root : V} {X : V → Twist k}
    (hroot : X root = 0) (a : k) :
    (fun v ↦ a • X v) root = 0 := by
  simp [hroot]

/-- On a nonzero assignment, the scalar parameter itself is recoverable.
This is the algebraic freeness statement behind the `G_m` orbit. -/
theorem commonScale_injective_of_ne_zero {X : V → Twist k} (hX : X ≠ 0) :
    Function.Injective (fun a : k ↦ (a • X : V → Twist k)) := by
  intro a b hab
  have hzero : (a - b) • X = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hab
  have habScalar : a - b = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact (hX h).elim
  exact sub_eq_zero.mp habScalar

/-- The multiplicative-group action is free on every nonzero assignment. -/
theorem units_commonScale_injective_of_ne_zero {X : V → Twist k} (hX : X ≠ 0) :
    Function.Injective (fun a : kˣ ↦ ((a : k) • X : V → Twist k)) := by
  intro a b hab
  apply Units.ext
  exact commonScale_injective_of_ne_zero hX hab

/-- A grounded assignment with at least two distinct labels is nonzero. -/
theorem ne_zero_of_grounded_of_ne {root v : V} {X : V → Twist k}
    (hroot : X root = 0) (hne : X v ≠ X root) : X ≠ 0 := by
  have hv : X v ≠ 0 := by
    simpa [hroot] using hne
  intro hX
  apply hv
  rw [hX]
  rfl

/-- Combined form used by the fixed-partition incidence stratum: after
grounding, any genuinely distinct block value has a free common-scaling
orbit, and every point of that orbit satisfies the same pin equations. -/
theorem grounded_scale_orbit_free_and_motion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    {root v : W} (hMotion : IsTwistMotion src dst p X)
    (hroot : X root = 0) (hne : X v ≠ X root) :
    Function.Injective (fun a : kˣ ↦ ((a : k) • X : W → Twist k)) ∧
      ∀ a : kˣ, IsTwistMotion src dst p (fun w ↦ (a : k) • X w) := by
  have hX : X ≠ 0 := ne_zero_of_grounded_of_ne hroot hne
  exact ⟨units_commonScale_injective_of_ne_zero hX,
    fun a ↦ hMotion.smul (a : k)⟩

end RB31E2E
