import RB31EndToEnd.NullCellule.ReplacementIdentities

/-!
# Provenance-preserving weight components

For the edge-to-`K₃` replacement, the old variable `y` has weight zero and
the displacement variable `d` has weight one.  This file proves inside
`MvPolynomial` that the three exact terms have weights `0`, `1`, and `2`.
Consequently the weight-zero initial component of the replaced equation is
literally the old edge equation.  This is the first formal descent statement;
it does not assume an initial-ideal or dimension theorem.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- The edge-to-triangle degeneration weight: the retained `y`-coordinates
have weight zero and the displacement `d`-coordinates have weight one. -/
def triangleWeight : TwistVariable (Fin 2) → ℕ :=
  fun x ↦ x.1.val

@[simp] theorem triangleWeight_zero (c : Bool × Fin 3) :
    triangleWeight (0, c) = 0 := rfl

@[simp] theorem triangleWeight_one (c : Bool × Fin 3) :
    triangleWeight (1, c) = 1 := rfl

theorem triangleY_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (i : Fin 3) :
    IsWeightedHomogeneous triangleWeight
      (X ((0 : Fin 2), b, i) : MvPolynomial (TwistVariable (Fin 2)) k) 0 := by
  simpa [triangleWeight] using
    (isWeightedHomogeneous_X k triangleWeight ((0 : Fin 2), b, i))

theorem triangleD_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (i : Fin 3) :
    IsWeightedHomogeneous triangleWeight
      (X ((1 : Fin 2), b, i) : MvPolynomial (TwistVariable (Fin 2)) k) 1 := by
  simpa [triangleWeight] using
    (isWeightedHomogeneous_X k triangleWeight ((1 : Fin 2), b, i))

theorem triangleA_isWeightedHomogeneous_zero
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight (triangleA (k := k)) 0 := by
  simp only [triangleA, Twist.splitKlein, Vec3.dot, triangleY,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 0
  intro i hi
  simpa using
    (triangleY_coordinate_isWeightedHomogeneous (k := k) false i).mul
      (triangleY_coordinate_isWeightedHomogeneous (k := k) true i)

theorem triangleC_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight (triangleC (k := k)) 2 := by
  simp only [triangleC, Twist.splitKlein, Vec3.dot, triangleD,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro i hi
  simpa using
    (triangleD_coordinate_isWeightedHomogeneous (k := k) false i).mul
      (triangleD_coordinate_isWeightedHomogeneous (k := k) true i)

theorem triangleMixed_isWeightedHomogeneous_one
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight
      (Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k))) 1 := by
  simp only [Twist.mixedPairing, Vec3.dot, triangleY, triangleD,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro i hi
    simpa using
      (triangleY_coordinate_isWeightedHomogeneous (k := k) false i).mul
        (triangleD_coordinate_isWeightedHomogeneous (k := k) true i)
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro i hi
    simpa using
      (triangleD_coordinate_isWeightedHomogeneous (k := k) false i).mul
        (triangleY_coordinate_isWeightedHomogeneous (k := k) true i)

/-- Exact three-layer provenance decomposition of the replacement equation. -/
theorem triangleB_eq_weight_layers {k : Type*} [CommRing k] :
    triangleB (k := k) =
      triangleA (k := k) +
        Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) +
          triangleC (k := k) := by
  rw [triangleB, triangleA, triangleC, triangleY, triangleD,
    Twist.splitKlein_add_mixedPairing]
  ac_rfl

/-- The weight-zero component descends exactly to the old edge equation. -/
theorem triangleB_weightedComponent_zero {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 0 (triangleB (k := k)) =
      triangleA (k := k) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_same]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_ne 0 (by decide)]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_ne 0 (by decide)]
  simp

/-- The weight-one component remembers precisely the mixed incidence term. -/
theorem triangleB_weightedComponent_one {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 1 (triangleB (k := k)) =
      Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne 1 (by decide)]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_same]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_ne 1 (by decide)]
  simp

/-- The weight-two component is exactly the new displacement null equation. -/
theorem triangleB_weightedComponent_two {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 2 (triangleB (k := k)) =
      triangleC (k := k) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne 2 (by decide)]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_ne 2 (by decide)]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_same]
  simp

end

end NullCellulePolynomial

end RB31E2E
