import RB31EndToEnd.API.BodyTwist

/-! A consumer of the public body-twist facade and no other project facade. -/

namespace PublicAPISmoke.BodyTwist

universe u

def expandedVec3 (k : Type u) : Type u :=
  Fin 3 → k

example (k : Type u) :
    RB31E2E.Vec3 k = expandedVec3 k :=
  rfl

example (k : Type u) :
    expandedVec3 k = RB31E2E.Vec3 k :=
  rfl

def expandedTwist (k : Type u) : Type u :=
  (Fin 3 → k) × (Fin 3 → k)

example (k : Type u) :
    RB31E2E.Twist k = expandedTwist k :=
  rfl

example (k : Type u) :
    expandedTwist k = RB31E2E.Twist k :=
  rfl

def dot
    {k : Type*} [CommSemiring k]
    (x y : RB31E2E.Vec3 k) : k :=
  RB31E2E.Vec3.dot x y

def cross
    {k : Type*} [CommRing k]
    (x y : RB31E2E.Vec3 k) : RB31E2E.Vec3 k :=
  RB31E2E.Vec3.cross x y

def eval
    {k : Type*} [CommRing k]
    (X : RB31E2E.Twist k) (p : RB31E2E.Vec3 k) :
    RB31E2E.Vec3 k :=
  RB31E2E.Twist.eval X p

def splitKlein
    {k : Type*} [CommRing k]
    (X : RB31E2E.Twist k) : k :=
  RB31E2E.Twist.splitKlein X

def compatibleAt
    {k : Type*} [CommRing k]
    (X Y : RB31E2E.Twist k) (p : RB31E2E.Vec3 k) : Prop :=
  RB31E2E.Twist.CompatibleAt X Y p

def isTwistMotion
    {k W E : Type*} [CommRing k]
    (src dst : E → W) (p : E → RB31E2E.Vec3 k)
    (X : W → RB31E2E.Twist k) : Prop :=
  RB31E2E.IsTwistMotion src dst p X

def isDiagonalTwist
    {k W : Type*} [CommRing k]
    (X : W → RB31E2E.Twist k) : Prop :=
  RB31E2E.IsDiagonalTwist X

def twistRigidAt
    {k W E : Type*} [CommRing k]
    (src dst : E → W) (p : E → RB31E2E.Vec3 k) : Prop :=
  RB31E2E.TwistRigidAt src dst p

def hasRigidTwistRealization
    {k W E : Type*} [CommRing k]
    (src dst : E → W) : Prop :=
  RB31E2E.HasRigidTwistRealization (k := k) src dst

def evalLinear
    {k : Type*} [Field k] (p : RB31E2E.Vec3 k) :
    RB31E2E.Twist k →ₗ[k] RB31E2E.Vec3 k :=
  RB31E2E.Twist.evalLinear p

def twoPinLinear
    {k : Type*} [Field k] (p q : RB31E2E.Vec3 k) :
    RB31E2E.Twist k →ₗ[k]
      (RB31E2E.Vec3 k × RB31E2E.Vec3 k) :=
  RB31E2E.Twist.twoPinLinear p q

example {k : Type*} [Field k] (p : RB31E2E.Vec3 k) :
    Module.finrank k
        (LinearMap.range (RB31E2E.Twist.evalLinear p)) ≤ 3 :=
  RB31E2E.Twist.finrank_range_evalLinear_le_three p

example {k : Type*} [Field k] (p q : RB31E2E.Vec3 k) :
    Module.finrank k
        (LinearMap.range (RB31E2E.Twist.twoPinLinear p q)) ≤ 5 :=
  RB31E2E.Twist.finrank_range_twoPinLinear_le_five p q

noncomputable def bundleLinear
    {k I : Type*} [Field k] (p : I → RB31E2E.Vec3 k) :
    RB31E2E.Twist k →ₗ[k] (I → RB31E2E.Vec3 k) :=
  RB31E2E.Twist.bundleLinear p

example {k : Type*} [Field k] (m : ℕ)
    (p : Fin m → RB31E2E.Vec3 k) :
    Module.finrank k
        (LinearMap.range (RB31E2E.Twist.bundleLinear p)) ≤
      RB31E2E.pinCapacity m :=
  RB31E2E.Twist.finrank_range_bundleLinear_le_pinCapacity m p

end PublicAPISmoke.BodyTwist
