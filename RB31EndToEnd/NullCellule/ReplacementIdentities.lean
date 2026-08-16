import RB31EndToEnd.NullCellule.PolynomialModel

/-!
# Exact polynomial identities for the two replacement moves

The weighted-degeneration argument later needs more than a dimension slogan:
it needs the exact provenance of every weight-zero, weight-one, and weight-two
term.  This file records those identities over an arbitrary commutative ring.
No initial-ideal or dimension theorem is assumed here.
-/

namespace RB31E2E

namespace Twist

variable {k : Type*} [CommRing k]

/-- The cross term in the polarization of the Split--Klein quadratic form.
It is `2B(X,Y)` in the paper's characteristic-not-two convention. -/
def mixedPairing (X Y : Twist k) : k :=
  Vec3.dot X.1 Y.2 + Vec3.dot Y.1 X.2

theorem splitKlein_add_mixedPairing (X Y : Twist k) :
    splitKlein (X + Y) =
      splitKlein X + splitKlein Y + mixedPairing X Y := by
  simp [splitKlein, mixedPairing, Vec3.dot, Fin.sum_univ_succ]
  ring

theorem mixedPairing_comm (X Y : Twist k) :
    mixedPairing X Y = mixedPairing Y X := by
  simp [mixedPairing, add_comm]

/-- Exact edge-to-`K₃` identity: `b-a-c` is the mixed term. -/
theorem splitKlein_add_sub_self_sub_self (X Y : Twist k) :
    splitKlein (X + Y) - splitKlein X - splitKlein Y =
      mixedPairing X Y := by
  rw [splitKlein_add_mixedPairing]
  abel

/-- Exact external-edge expansion for vertex-to-`K₄`. -/
theorem splitKlein_translate_difference (Z D A : Twist k) :
    splitKlein ((Z + D) - A) =
      splitKlein (Z - A) + splitKlein D + mixedPairing (Z - A) D := by
  rw [show (Z + D) - A = (Z - A) + D by abel,
    splitKlein_add_mixedPairing]

/-- Common translation cancels from an internal clone edge. -/
theorem splitKlein_common_translate_difference (Z D₁ D₂ : Twist k) :
    splitKlein ((Z + D₁) - (Z + D₂)) = splitKlein (D₁ - D₂) := by
  congr 1
  abel

end Twist

namespace NullCellulePolynomial

noncomputable section

/-- Two provenance-labelled polynomial twists used as the local `y,d`
coordinates of the edge-to-`K₃` move. -/
def triangleY {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable (Fin 2)) k) :=
  universalTwist 0

def triangleD {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable (Fin 2)) k) :=
  universalTwist 1

def triangleA {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleY (k := k))

def triangleB {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleY (k := k) + triangleD (k := k))

def triangleC {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleD (k := k))

/-- Polynomial-level form of `b-a-c = 2B(y,d)`, retaining the `y/d`
variable provenance needed by the six local initial-fibre cases. -/
theorem triangle_polar_combination {k : Type*} [CommRing k] :
    triangleB (k := k) - triangleA (k := k) - triangleC (k := k) =
      Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) := by
  exact Twist.splitKlein_add_sub_self_sub_self _ _

end

end NullCellulePolynomial

end RB31E2E
