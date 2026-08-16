import Mathlib

/-!
# Three-dimensional twists and the Split--Klein form

This file contains only explicit linear algebra.  A twist is an angular
velocity together with a translational velocity.  Its value at a point
is the usual infinitesimal rigid-body velocity.  No rigidity theorem is
assumed here.
-/

namespace RB31E2E

/-- Coordinate vectors in dimension three. -/
abbrev Vec3 (k : Type*) := Fin 3 → k

namespace Vec3

/-- The bilinear coordinate dot product (not a Hermitian product). -/
def dot {k : Type*} [CommSemiring k] (x y : Vec3 k) : k :=
  ∑ i, x i * y i

/-- The coordinate cross product. -/
def cross {k : Type*} [CommRing k] (x y : Vec3 k) : Vec3 k :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

@[simp] theorem cross_self {k : Type*} [CommRing k] (x : Vec3 k) :
    cross x x = 0 := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_sub_left {k : Type*} [CommRing k] (x y p : Vec3 k) :
    cross (x - y) p = cross x p - cross y p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_add_left {k : Type*} [CommRing k] (x y p : Vec3 k) :
    cross (x + y) p = cross x p + cross y p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_left {k : Type*} [CommRing k] (a : k) (x p : Vec3 k) :
    cross (a • x) p = a • cross x p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem dot_cross_self_left {k : Type*} [CommRing k] (x p : Vec3 k) :
    dot x (cross x p) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

end Vec3

/-- Angular and translational parts of an infinitesimal rigid motion. -/
abbrev Twist (k : Type*) := Vec3 k × Vec3 k

namespace Twist

/-- Velocity induced by a twist at the point `p`. -/
def eval {k : Type*} [CommRing k] (X : Twist k) (p : Vec3 k) : Vec3 k :=
  X.2 + Vec3.cross X.1 p

/-- The split Klein quadratic polynomial `ω · v`. -/
def splitKlein {k : Type*} [CommRing k] (X : Twist k) : k :=
  Vec3.dot X.1 X.2

@[simp] theorem splitKlein_neg {k : Type*} [CommRing k] (X : Twist k) :
    splitKlein (-X) = splitKlein X := by
  simp [splitKlein, Vec3.dot]

theorem splitKlein_sub_comm {k : Type*} [CommRing k] (X Y : Twist k) :
    splitKlein (X - Y) = splitKlein (Y - X) := by
  rw [show Y - X = -(X - Y) by abel, splitKlein_neg]

theorem splitKlein_smul {k : Type*} [CommRing k] (a : k) (X : Twist k) :
    splitKlein (a • X) = a ^ 2 * splitKlein X := by
  simp [splitKlein, Vec3.dot, Fin.sum_univ_succ]
  ring

/-- Two body twists assign the same velocity to the shared pin. -/
def CompatibleAt {k : Type*} [CommRing k]
    (X Y : Twist k) (p : Vec3 k) : Prop :=
  eval X p = eval Y p

theorem eval_sub {k : Type*} [CommRing k] (X Y : Twist k) (p : Vec3 k) :
    eval (X - Y) p = eval X p - eval Y p := by
  change (X.2 - Y.2) + Vec3.cross (X.1 - Y.1) p =
    (X.2 + Vec3.cross X.1 p) - (Y.2 + Vec3.cross Y.1 p)
  rw [Vec3.cross_sub_left]
  abel

theorem splitKlein_eq_zero_of_eval_eq_zero {k : Type*} [CommRing k]
    (X : Twist k) (p : Vec3 k) (h : eval X p = 0) :
    splitKlein X = 0 := by
  have hv : X.2 = -Vec3.cross X.1 p := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [eval] using h
  rw [splitKlein, hv]
  simp only [Vec3.dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  change -Vec3.dot X.1 (Vec3.cross X.1 p) = 0
  rw [Vec3.dot_cross_self_left]
  exact neg_zero

theorem splitKlein_sub_eq_zero_of_compatibleAt {k : Type*} [CommRing k]
    (X Y : Twist k) (p : Vec3 k) (h : CompatibleAt X Y p) :
    splitKlein (X - Y) = 0 := by
  apply splitKlein_eq_zero_of_eval_eq_zero (X - Y) p
  rw [eval_sub]
  exact sub_eq_zero.mpr h

end Twist

end RB31E2E
