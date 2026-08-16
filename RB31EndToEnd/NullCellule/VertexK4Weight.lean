import RB31EndToEnd.NullCellule.WeightComponents

/-!
# Provenance weights for the vertex-to-`K₄` replacement

The retained centre twist `Z` and an external twist `A` have weight zero,
whereas the three clone displacements `D i` have weight one.  This file
records the resulting `0/1/2` decomposition of every external clone-edge
equation.  It also proves that common translation cancels on an internal
clone edge and that the resulting equation is purely of weight two.

The vertex labels below are deliberately explicit: the three displacement
labels remain distinguishable throughout the polynomial calculation.  Thus
the statements retain the provenance needed by a later initial-ideal or
incidence-descent argument; no such geometric theorem is assumed here.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- Provenance labels for one vertex-to-`K₄` replacement chart. -/
inductive VertexK4Label
  | center
  | external
  | displacement (i : Fin 3)
  deriving DecidableEq

/-- The retained central twist. -/
def vertexK4Z {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist VertexK4Label.center

/-- A provenance-labelled external twist. -/
def vertexK4A {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist VertexK4Label.external

/-- The displacement of clone `i` from the retained centre. -/
def vertexK4D {k : Type*} [CommRing k] (i : Fin 3) :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist (VertexK4Label.displacement i)

/-- Centre and external coordinates have weight zero; every clone
displacement coordinate has weight one. -/
def vertexK4Weight : TwistVariable VertexK4Label → ℕ
  | ⟨VertexK4Label.center, _⟩ => 0
  | ⟨VertexK4Label.external, _⟩ => 0
  | ⟨VertexK4Label.displacement _, _⟩ => 1

@[simp] theorem vertexK4Weight_center (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.center, c) = 0 := rfl

@[simp] theorem vertexK4Weight_external (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.external, c) = 0 := rfl

@[simp] theorem vertexK4Weight_displacement (i : Fin 3)
    (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.displacement i, c) = 1 := rfl

theorem vertexK4Z_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.center, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.center, b, j))

theorem vertexK4A_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.external, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.external, b, j))

theorem vertexK4D_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (i : Fin 3) (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.displacement i, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 1 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.displacement i, b, j))

/-- The old external edge equation, before the centre is cloned. -/
def vertexK4OldExternal {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4Z (k := k) - vertexK4A (k := k))

/-- The equation on the external edge incident with clone `i`. -/
def vertexK4ExternalClone {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein
    ((vertexK4Z (k := k) + vertexK4D (k := k) i) - vertexK4A (k := k))

/-- The mixed centre/external--displacement term for clone `i`. -/
def vertexK4ExternalMixed {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.mixedPairing
    (vertexK4Z (k := k) - vertexK4A (k := k))
    (vertexK4D (k := k) i)

/-- The pure displacement-null term for clone `i`. -/
def vertexK4DisplacementNull {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4D (k := k) i)

/-- The internal clone-edge equation between clones `i` and `j`. -/
def vertexK4InternalClone {k : Type*} [CommRing k] (i j : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein
    ((vertexK4Z (k := k) + vertexK4D (k := k) i) -
      (vertexK4Z (k := k) + vertexK4D (k := k) j))

/-- The same internal edge written only in displacement coordinates. -/
def vertexK4InternalDisplacement {k : Type*} [CommRing k] (i j : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4D (k := k) i - vertexK4D (k := k) j)

private theorem vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.center, b, j) -
        X (VertexK4Label.external, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  exact (weightedHomogeneousSubmodule k vertexK4Weight 0).sub_mem
    (vertexK4Z_coordinate_isWeightedHomogeneous (k := k) b j)
    (vertexK4A_coordinate_isWeightedHomogeneous (k := k) b j)

private theorem vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (i j : Fin 3) (b : Bool) (r : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.displacement i, b, r) -
        X (VertexK4Label.displacement j, b, r) :
        MvPolynomial (TwistVariable VertexK4Label) k) 1 := by
  exact (weightedHomogeneousSubmodule k vertexK4Weight 1).sub_mem
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i b r)
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) j b r)

theorem vertexK4OldExternal_isWeightedHomogeneous_zero
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous vertexK4Weight (vertexK4OldExternal (k := k)) 0 := by
  simp only [vertexK4OldExternal, Twist.splitKlein, Vec3.dot, vertexK4Z,
    vertexK4A, universalTwist]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 0
  intro j hj
  simpa using
    (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) false j).mul
      (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) true j)

theorem vertexK4DisplacementNull_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4DisplacementNull (k := k) i) 2 := by
  simp only [vertexK4DisplacementNull, Twist.splitKlein, Vec3.dot, vertexK4D,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro j hj
  simpa using
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i false j).mul
      (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i true j)

theorem vertexK4ExternalMixed_isWeightedHomogeneous_one
    {k : Type*} [CommRing k] (i : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4ExternalMixed (k := k) i) 1 := by
  simp only [vertexK4ExternalMixed, Twist.mixedPairing, Vec3.dot, vertexK4Z,
    vertexK4A, vertexK4D, universalTwist, angularCoordinate,
    translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro j hj
    simpa using
      (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) false j).mul
        (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i true j)
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro j hj
    simpa using
      (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i false j).mul
        (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) true j)

/-- Exact `0/1/2` provenance decomposition of every external clone edge. -/
theorem vertexK4ExternalClone_eq_weight_layers
    {k : Type*} [CommRing k] (i : Fin 3) :
    vertexK4ExternalClone (k := k) i =
      vertexK4OldExternal (k := k) +
        vertexK4ExternalMixed (k := k) i +
          vertexK4DisplacementNull (k := k) i := by
  rw [vertexK4ExternalClone, vertexK4OldExternal, vertexK4ExternalMixed,
    vertexK4DisplacementNull, Twist.splitKlein_translate_difference]
  ac_rfl

/-- The weight-zero component is literally the original external edge. -/
theorem vertexK4ExternalClone_weightedComponent_zero
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 0
        (vertexK4ExternalClone (k := k) i) =
      vertexK4OldExternal (k := k) := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_same]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_ne
    0 (by decide)]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_ne
    0 (by decide)]
  simp

/-- The weight-one component is precisely the mixed incidence term. -/
theorem vertexK4ExternalClone_weightedComponent_one
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 1
        (vertexK4ExternalClone (k := k) i) =
      vertexK4ExternalMixed (k := k) i := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne
    1 (by decide)]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_same]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_ne
    1 (by decide)]
  simp

/-- The weight-two component is precisely the displacement null term. -/
theorem vertexK4ExternalClone_weightedComponent_two
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 2
        (vertexK4ExternalClone (k := k) i) =
      vertexK4DisplacementNull (k := k) i := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne
    2 (by decide)]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_ne
    2 (by decide)]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_same]
  simp

/-- Common translation by `Z` cancels exactly on an internal clone edge. -/
theorem vertexK4InternalClone_eq_internalDisplacement
    {k : Type*} [CommRing k] (i j : Fin 3) :
    vertexK4InternalClone (k := k) i j =
      vertexK4InternalDisplacement (k := k) i j := by
  exact Twist.splitKlein_common_translate_difference _ _ _

/-- An internal clone edge is purely of provenance weight two. -/
theorem vertexK4InternalDisplacement_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4InternalDisplacement (k := k) i j) 2 := by
  simp only [vertexK4InternalDisplacement, Twist.splitKlein, Vec3.dot,
    vertexK4D, universalTwist]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro r hr
  simpa using
    (vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
      (k := k) i j false r).mul
      (vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
        (k := k) i j true r)

theorem vertexK4InternalClone_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4InternalClone (k := k) i j) 2 := by
  rw [vertexK4InternalClone_eq_internalDisplacement]
  exact vertexK4InternalDisplacement_isWeightedHomogeneous_two i j

/-- The internal clone edge has no weight-zero contribution. -/
theorem vertexK4InternalClone_weightedComponent_zero
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 0
        (vertexK4InternalClone (k := k) i j) = 0 := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_ne
    0 (by decide)

/-- The internal clone edge has no weight-one contribution. -/
theorem vertexK4InternalClone_weightedComponent_one
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 1
        (vertexK4InternalClone (k := k) i j) = 0 := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_ne
    1 (by decide)

/-- The entire internal clone-edge equation is its weight-two component. -/
theorem vertexK4InternalClone_weightedComponent_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 2
        (vertexK4InternalClone (k := k) i j) =
      vertexK4InternalClone (k := k) i j := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_same

end

end NullCellulePolynomial

end RB31E2E
