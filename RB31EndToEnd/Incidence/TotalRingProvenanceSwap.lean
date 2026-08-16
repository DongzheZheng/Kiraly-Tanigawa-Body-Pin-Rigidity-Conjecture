import RB31EndToEnd.Incidence.UniversalHomogeneousChart
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Swapping the two provenance layers in the total incidence ring

The universal homogeneous chart is written as

`Q[pin][twist] = MvPolynomial twist (MvPolynomial pin Q)`.

For active-pin elimination it is useful to regard the same total ring as

`Q[twist][pin] = MvPolynomial pin (MvPolynomial twist Q)`.

This file implements that change of viewpoint with
`MvPolynomial.commAlgEquiv`.  In the swapped presentation every pin
coordinate is an outer polynomial variable, while every grounded-twist
coordinate lies in the coefficient ring.  The final theorem computes the
image of an actual universal compatibility coordinate in these explicit
swapped coordinates.
-/

namespace RB31E2E

namespace TotalRingProvenanceSwap

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart

/-! ## The swapped total ring -/

/-- The same total polynomial algebra as `RelativeRing`, with pin variables
on the outside and grounded-twist variables in the coefficient ring. -/
abbrev PinOuterRing {V : Type*} (root : V) (E : Type*) :=
  MvPolynomial (PinVariable E)
    (MvPolynomial (GroundedTwistVariable root) ℚ)

/-- Exchange the pin and grounded-twist polynomial layers. -/
def totalRingSwap {V E : Type*} (root : V) :
    RelativeRing root E ≃ₐ[ℚ] PinOuterRing root E :=
  MvPolynomial.commAlgEquiv ℚ
    (GroundedTwistVariable root) (PinVariable E)

/-- The underlying ring homomorphism of `totalRingSwap`, convenient for the
coordinatewise maps on vectors and twists. -/
abbrev totalRingSwapHom {V E : Type*} (root : V) :
    RelativeRing root E →+* PinOuterRing root E :=
  (totalRingSwap (E := E) root).toRingEquiv.toRingHom

@[simp]
theorem totalRingSwap_pinVariable {V E : Type*} (root : V)
    (p : PinVariable E) :
    totalRingSwap (E := E) root (C (X p)) = X p := by
  exact MvPolynomial.commAlgEquiv_C_X p

@[simp]
theorem totalRingSwap_twistVariable {V E : Type*} (root : V)
    (c : GroundedTwistVariable root) :
    totalRingSwap (E := E) root (X c) = C (X c) := by
  exact MvPolynomial.commAlgEquiv_X c

@[simp]
theorem totalRingSwapHom_pinVariable {V E : Type*} (root : V)
    (p : PinVariable E) :
    totalRingSwapHom (E := E) root (C (X p)) = X p := by
  exact totalRingSwap_pinVariable root p

@[simp]
theorem totalRingSwapHom_twistVariable {V E : Type*} (root : V)
    (c : GroundedTwistVariable root) :
    totalRingSwapHom (E := E) root (X c) = C (X c) := by
  exact totalRingSwap_twistVariable root c

/-! ## Explicit pins and twists after the swap -/

/-- The universal pin after the swap: its three coordinates are now outer
pin variables rather than coefficients. -/
def pinOuterUniversalPin {V E : Type*} (root : V) (e : E) :
    Vec3 (PinOuterRing root E) :=
  fun i ↦ X ⟨e, i⟩

/-- One off-root universal twist after the swap: its six coordinates are
coefficients in the inner twist-polynomial ring. -/
def pinOuterOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) : Twist (PinOuterRing root E) :=
  ⟨fun i ↦ C (X ⟨w, ⟨false, i⟩⟩),
    fun i ↦ C (X ⟨w, ⟨true, i⟩⟩)⟩

/-- The root-zero universal twist assignment in the swapped presentation. -/
def pinOuterGroundedTwist {V E : Type*} [DecidableEq V] (root : V) :
    V → Twist (PinOuterRing root E) :=
  extendOffRoot root (fun w ↦ pinOuterOffRootTwist (E := E) w)

/-- The relative twist for an oriented occurrence in the swapped
presentation. -/
def pinOuterRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (PinOuterRing root E) :=
  pinOuterGroundedTwist (E := E) root (src e) -
    pinOuterGroundedTwist (E := E) root (dst e)

@[simp]
theorem map_universalParameterPin {V E : Type*} (root : V) (e : E) :
    mapVec3 (totalRingSwapHom (E := E) root)
        (universalParameterPin (root := root) e) =
      pinOuterUniversalPin root e := by
  funext i
  simp [mapVec3, universalParameterPin, pinOuterUniversalPin]

@[simp]
theorem map_universalOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalOffRootTwist (E := E) w) =
      pinOuterOffRootTwist (E := E) w := by
  apply Prod.ext <;> funext i <;>
    simp [mapTwist, mapVec3, universalOffRootTwist,
      pinOuterOffRootTwist]

@[simp]
theorem map_universalGroundedTwist {V E : Type*} [DecidableEq V]
    (root v : V) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalGroundedTwist (E := E) root v) =
      pinOuterGroundedTwist (E := E) root v := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist, pinOuterGroundedTwist,
      extendOffRoot]
  · simp only [universalGroundedTwist, pinOuterGroundedTwist,
      extendOffRoot, hv, dite_false]
    exact map_universalOffRootTwist (E := E) ⟨v, hv⟩

@[simp]
theorem map_universalRelativeTwist {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) :
    mapTwist (totalRingSwapHom (E := E) root)
        (universalRelativeTwist root src dst e) =
      pinOuterRelativeTwist root src dst e := by
  rw [universalRelativeTwist, mapTwist_sub,
    map_universalGroundedTwist, map_universalGroundedTwist]
  rfl

/-! ## Compatibility coordinates in the pin-outer presentation -/

/-- The actual universal compatibility coordinate after changing the order
of the two polynomial layers.  This is the concrete generator-level bridge:
the pin coordinates on the right are outer variables, whereas every twist
coordinate is a coefficient. -/
theorem totalRingSwap_universalCompatibilityCoordinate
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    totalRingSwap (E := E) root
        (universalCompatibilityCoordinate root src dst e j) =
      Twist.eval (pinOuterRelativeTwist root src dst e)
        (pinOuterUniversalPin root e) j := by
  change totalRingSwapHom (E := E) root
      (Twist.eval (universalRelativeTwist root src dst e)
        (universalParameterPin (root := root) e) j) = _
  calc
    _ = Twist.eval
        (mapTwist (totalRingSwapHom (E := E) root)
          (universalRelativeTwist root src dst e))
        (mapVec3 (totalRingSwapHom (E := E) root)
          (universalParameterPin (root := root) e)) j :=
      congrFun
        (mapVec3_eval (totalRingSwapHom (E := E) root)
          (universalRelativeTwist root src dst e)
          (universalParameterPin (root := root) e)) j
    _ = _ := by
      rw [map_universalRelativeTwist, map_universalParameterPin]

end

end TotalRingProvenanceSwap

end RB31E2E
