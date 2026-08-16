import RB31EndToEnd.Linear.Vec3Twist

/-!
# Occurrence-level body twist systems

The endpoints are arbitrary functions on an occurrence type.  This
keeps parallel pins distinct and makes the semantics independent of a
chosen graph library representation.
-/

namespace RB31E2E

variable {k W E : Type*} [CommRing k]

/-- Every pin occurrence receives the same velocity from its two bodies. -/
def IsTwistMotion (src dst : E → W) (p : E → Vec3 k)
    (X : W → Twist k) : Prop :=
  ∀ e, Twist.eval (X (src e)) (p e) = Twist.eval (X (dst e)) (p e)

/-- A twist assignment is a single global Euclidean infinitesimal motion. -/
def IsDiagonalTwist (X : W → Twist k) : Prop :=
  ∃ Y : Twist k, X = fun _ ↦ Y

/-- At this pin placement the only body-twist motions are diagonal. -/
def TwistRigidAt (src dst : E → W) (p : E → Vec3 k) : Prop :=
  ∀ X : W → Twist k, IsTwistMotion src dst p X → IsDiagonalTwist X

/-- There exists a pin placement at which the twist system is rigid. -/
def HasRigidTwistRealization (src dst : E → W) : Prop :=
  ∃ p : E → Vec3 k, TwistRigidAt src dst p

theorem isTwistMotion_swap (src dst : E → W) (p : E → Vec3 k)
    (X : W → Twist k) :
    IsTwistMotion src dst p X ↔ IsTwistMotion dst src p X := by
  constructor <;> intro h e <;> exact (h e).symm

theorem twistRigidAt_swap (src dst : E → W) (p : E → Vec3 k) :
    TwistRigidAt src dst p ↔ TwistRigidAt dst src p := by
  constructor <;> intro h X hX
  · exact h X ((isTwistMotion_swap src dst p X).mpr hX)
  · exact h X ((isTwistMotion_swap src dst p X).mp hX)

theorem hasRigidTwistRealization_swap (src dst : E → W) :
    HasRigidTwistRealization (k := k) src dst ↔
      HasRigidTwistRealization (k := k) dst src := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (twistRigidAt_swap src dst p).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (twistRigidAt_swap src dst p).mpr hp⟩

theorem isTwistMotion_diagonal (src dst : E → W) (p : E → Vec3 k)
    (Y : Twist k) :
    IsTwistMotion src dst p (fun _ ↦ Y) := by
  intro e
  rfl

theorem IsDiagonalTwist.isTwistMotion {src dst : E → W} {p : E → Vec3 k}
    {X : W → Twist k} (hX : IsDiagonalTwist X) :
    IsTwistMotion src dst p X := by
  obtain ⟨Y, rfl⟩ := hX
  exact isTwistMotion_diagonal src dst p Y

theorem eval_sub_eq_zero_of_isTwistMotion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    (hX : IsTwistMotion src dst p X) (e : E) :
    Twist.eval (X (src e) - X (dst e)) (p e) = 0 := by
  rw [Twist.eval_sub]
  exact sub_eq_zero.mpr (hX e)

/-- Pin compatibility forces a Split--Klein null difference. -/
theorem splitKlein_sub_eq_zero_of_isTwistMotion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    (hX : IsTwistMotion src dst p X) (e : E) :
    Twist.splitKlein (X (src e) - X (dst e)) = 0 :=
  Twist.splitKlein_sub_eq_zero_of_compatibleAt _ _ _ (hX e)

end RB31E2E
