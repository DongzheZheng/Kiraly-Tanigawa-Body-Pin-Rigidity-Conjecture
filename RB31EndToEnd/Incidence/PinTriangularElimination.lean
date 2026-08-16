import RB31EndToEnd.Incidence.UniversalHomogeneousChart

/-!
# Triangular elimination of one active pin

Fix a nonzero angular coordinate `i` of a relative twist.  A stationary pin
then has one free coordinate, namely its `i`-th coordinate.  The other two
compatibility coordinates are triangular: after clearing the single angular
denominator they are exactly the two private-pin coordinate relations.

This file proves that statement first over an arbitrary commutative ring and
then in the provenance-retaining universal homogeneous chart.  In particular,
the two denominator-cleared private-coordinate relations generate exactly the
same ideal as the selected pair of compatibility coordinates.  No height or
codimension conclusion is made here.
-/

namespace RB31E2E

namespace PinTriangularElimination

noncomputable section

open MvPolynomial
open UniversalHomogeneousChart

/-! ## The two private coordinates in each angular chart -/

/-- The two pin coordinates other than the free chart coordinate `i`. -/
def privateCoordinate (i : Fin 3) (slot : Fin 2) : Fin 3 :=
  if i = 0 then
    if slot = 0 then 1 else 2
  else if i = 1 then
    if slot = 0 then 0 else 2
  else
    if slot = 0 then 0 else 1

/-- The compatibility coordinate which solves the corresponding private pin
coordinate.  The order is chosen to agree with `privateCoordinate`. -/
def solvingCompatibilityCoordinate (i : Fin 3) (slot : Fin 2) : Fin 3 :=
  if i = 0 then
    if slot = 0 then 2 else 1
  else if i = 1 then
    if slot = 0 then 2 else 0
  else
    if slot = 0 then 1 else 0

theorem privateCoordinate_ne (i : Fin 3) (slot : Fin 2) :
    privateCoordinate i slot ≠ i := by
  fin_cases i <;> fin_cases slot <;> decide

theorem privateCoordinate_injective (i : Fin 3) :
    Function.Injective (privateCoordinate i) := by
  intro a b hab
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [privateCoordinate] at hab ⊢

/-! ## Denominator-cleared chart relations over an arbitrary ring -/

/-- The numerator vector in the angular chart `i`.  Dividing it by `Z.1 i`
gives the stationary-pin formula; its `i`-th entry is deliberately
`Z.1 i * p i`, so that only the other two entries carry information. -/
def stationaryPinNumerator {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Vec3 R :=
  if i = 0 then
    ![Z.1 0 * p 0,
      Z.1 1 * p 0 - Z.2 2,
      Z.2 1 + Z.1 2 * p 0]
  else if i = 1 then
    ![Z.2 2 + Z.1 0 * p 1,
      Z.1 1 * p 1,
      Z.1 2 * p 1 - Z.2 0]
  else
    ![Z.1 0 * p 2 - Z.2 1,
      Z.2 0 + Z.1 1 * p 2,
      Z.1 2 * p 2]

/-- One denominator-cleared private-coordinate relation. -/
def triangularResidual {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  Z.1 i * p (privateCoordinate i slot) -
    stationaryPinNumerator Z p i (privateCoordinate i slot)

/-- The selected compatibility equation, without the harmless orientation
sign appearing in the triangular identity. -/
def selectedCompatibilityEquation {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  Twist.eval Z p (solvingCompatibilityCoordinate i slot)

/-- Orient the selected compatibility equation so that it is literally the
denominator-cleared private-coordinate residual. -/
def orientedCompatibilityEquation {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) : R :=
  if i = 0 then
    if slot = 0 then Twist.eval Z p 2 else -Twist.eval Z p 1
  else if i = 1 then
    if slot = 0 then -Twist.eval Z p 2 else Twist.eval Z p 0
  else
    if slot = 0 then Twist.eval Z p 1 else -Twist.eval Z p 0

/-- The six cross-product calculations, packaged as one uniform triangular
identity. -/
theorem triangularResidual_eq_orientedCompatibilityEquation
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    triangularResidual Z p i slot =
      orientedCompatibilityEquation Z p i slot := by
  fin_cases i <;> fin_cases slot <;>
    simp [triangularResidual, stationaryPinNumerator, privateCoordinate,
      orientedCompatibilityEquation, Twist.eval, Vec3.cross] <;> ring

/-- Orientation changes only a sign; provenance and the selected
compatibility coordinate are unchanged. -/
theorem orientedCompatibilityEquation_eq_selected_or_neg
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    orientedCompatibilityEquation Z p i slot =
        selectedCompatibilityEquation Z p i slot ∨
      orientedCompatibilityEquation Z p i slot =
        -selectedCompatibilityEquation Z p i slot := by
  fin_cases i <;> fin_cases slot <;>
    simp [orientedCompatibilityEquation, selectedCompatibilityEquation,
      solvingCompatibilityCoordinate]

/-- The ideal of the two compatibility coordinates selected by chart `i`. -/
def compatibilityPairIdeal {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal R :=
  Ideal.span (Set.range (selectedCompatibilityEquation Z p i))

/-- The ideal of the two denominator-cleared private-pin relations. -/
def triangularResidualIdeal {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal R :=
  Ideal.span (Set.range (triangularResidual Z p i))

private theorem orientedCompatibilityEquation_mem_compatibilityPairIdeal
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    orientedCompatibilityEquation Z p i slot ∈
      compatibilityPairIdeal Z p i := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · rw [h]
    exact (compatibilityPairIdeal Z p i).neg_mem
      (Ideal.subset_span ⟨slot, rfl⟩)

private theorem selectedCompatibilityEquation_mem_orientedSpan
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    selectedCompatibilityEquation Z p i slot ∈
      Ideal.span (Set.range (orientedCompatibilityEquation Z p i)) := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · have hm : -selectedCompatibilityEquation Z p i slot ∈
        Ideal.span (Set.range (orientedCompatibilityEquation Z p i)) := by
      rw [← h]
      exact Ideal.subset_span ⟨slot, rfl⟩
    simpa using
      (Ideal.span (Set.range (orientedCompatibilityEquation Z p i))).neg_mem hm

/-- The two compatibility equations and the two denominator-cleared
private-coordinate relations generate exactly the same ideal.  This is an
identity over the original ring; no localization or dimension theorem is
needed. -/
theorem triangularResidualIdeal_eq_compatibilityPairIdeal
    {R : Type*} [CommRing R]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) :
    triangularResidualIdeal Z p i = compatibilityPairIdeal Z p i := by
  apply le_antisymm
  · rw [triangularResidualIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    rw [triangularResidual_eq_orientedCompatibilityEquation]
    exact orientedCompatibilityEquation_mem_compatibilityPairIdeal
      Z p i slot
  · rw [compatibilityPairIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    rw [triangularResidualIdeal]
    have h := selectedCompatibilityEquation_mem_orientedSpan Z p i slot
    have hfun : triangularResidual Z p i =
        orientedCompatibilityEquation Z p i := by
      funext s
      exact triangularResidual_eq_orientedCompatibilityEquation Z p i s
    rwa [hfun]

/-! ## The same elimination after inverting the angular coordinate -/

/-- The distinguished angular coordinate as a unit in any away
localization at that coordinate. -/
def localizedAngularUnit
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (i : Fin 3) [IsLocalization.Away (Z.1 i) A] : Aˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := A) (Z.1 i)).unit

@[simp]
theorem localizedAngularUnit_coe
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (i : Fin 3) [IsLocalization.Away (Z.1 i) A] :
    ((localizedAngularUnit (A := A) Z i : Aˣ) : A) =
      algebraMap R A (Z.1 i) := by
  exact (IsLocalization.Away.algebraMap_isUnit (S := A) (Z.1 i)).unit_spec

/-- The normalized relation `p_j - numerator_j / ω_i`, represented in an
arbitrary away localization by multiplying the cleared residual by the
inverse of the distinguished angular unit. -/
def normalizedPrivateRelation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2)
    [IsLocalization.Away (Z.1 i) A] : A :=
  (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
    algebraMap R A (triangularResidual Z p i slot)

/-- The normalized relation is literally a private pin coordinate minus its
rational chart expression. -/
theorem normalizedPrivateRelation_eq_coordinate_sub_fraction
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2)
    [IsLocalization.Away (Z.1 i) A] :
    normalizedPrivateRelation (A := A) Z p i slot =
      algebraMap R A (p (privateCoordinate i slot)) -
        (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
          algebraMap R A
            (stationaryPinNumerator Z p i (privateCoordinate i slot)) := by
  rw [normalizedPrivateRelation, triangularResidual, map_sub, map_mul,
    ← localizedAngularUnit_coe (A := A) Z i]
  rw [mul_sub, ← mul_assoc, Units.inv_mul, one_mul]

/-- The selected compatibility pair after applying the away-localization
map. -/
def localizedCompatibilityPairIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) : Ideal A :=
  Ideal.span (Set.range (fun slot : Fin 2 ↦
    algebraMap R A (selectedCompatibilityEquation Z p i slot)))

/-- The two normalized private-coordinate relations in the away chart. -/
def normalizedPrivateRelationIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A] : Ideal A :=
  Ideal.span (Set.range (fun slot : Fin 2 ↦
    normalizedPrivateRelation (A := A) Z p i slot))

private theorem mapped_orientedCompatibility_mem_localizedPair
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3) (slot : Fin 2) :
    algebraMap R A (orientedCompatibilityEquation Z p i slot) ∈
      localizedCompatibilityPairIdeal (A := A) Z p i := by
  rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
  · rw [h]
    exact Ideal.subset_span ⟨slot, rfl⟩
  · rw [h, map_neg]
    exact (localizedCompatibilityPairIdeal (A := A) Z p i).neg_mem
      (Ideal.subset_span ⟨slot, rfl⟩)

/-- After inverting `Z.1 i`, the two compatibility coordinates generate
exactly the ideal of the two explicit rational private-coordinate
relations. -/
theorem localizedCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Z : Twist R) (p : Vec3 R) (i : Fin 3)
    [IsLocalization.Away (Z.1 i) A] :
    localizedCompatibilityPairIdeal (A := A) Z p i =
      normalizedPrivateRelationIdeal (A := A) Z p i := by
  apply le_antisymm
  · rw [localizedCompatibilityPairIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    let J := normalizedPrivateRelationIdeal (A := A) Z p i
    have hn : normalizedPrivateRelation (A := A) Z p i slot ∈ J :=
      Ideal.subset_span ⟨slot, rfl⟩
    have hu := J.mul_mem_left
      ((localizedAngularUnit (A := A) Z i : Aˣ) : A) hn
    have hres : algebraMap R A (triangularResidual Z p i slot) ∈ J := by
      rw [normalizedPrivateRelation, ← mul_assoc, Units.mul_inv, one_mul] at hu
      exact hu
    have hor : algebraMap R A
        (orientedCompatibilityEquation Z p i slot) ∈ J := by
      rwa [triangularResidual_eq_orientedCompatibilityEquation] at hres
    rcases orientedCompatibilityEquation_eq_selected_or_neg Z p i slot with h | h
    · simpa only [h] using hor
    · have hneg := J.neg_mem hor
      simpa only [h, map_neg, neg_neg] using hneg
  · rw [normalizedPrivateRelationIdeal, Ideal.span_le]
    rintro _ ⟨slot, rfl⟩
    change (((localizedAngularUnit (A := A) Z i)⁻¹ : Aˣ) : A) *
      algebraMap R A (triangularResidual Z p i slot) ∈
        localizedCompatibilityPairIdeal (A := A) Z p i
    apply (localizedCompatibilityPairIdeal (A := A) Z p i).mul_mem_left
    rw [triangularResidual_eq_orientedCompatibilityEquation]
    exact mapped_orientedCompatibility_mem_localizedPair Z p i slot

/-- Concrete `Localization.Away` form of the preceding theorem. -/
theorem awayCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    {R : Type*} [CommRing R] (Z : Twist R) (p : Vec3 R) (i : Fin 3) :
    localizedCompatibilityPairIdeal
        (A := Localization.Away (Z.1 i)) Z p i =
      normalizedPrivateRelationIdeal
        (A := Localization.Away (Z.1 i)) Z p i := by
  exact localizedCompatibilityPairIdeal_eq_normalizedPrivateRelationIdeal
    Z p i

/-! ## Specialization to the universal homogeneous chart -/

/-- The selected private-coordinate relation with both provenance layers
retained. -/
def universalTriangularResidual
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) : RelativeRing root E :=
  triangularResidual
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i slot

/-- The sign-oriented pair written directly in terms of the named universal
compatibility coordinates. -/
def universalOrientedCompatibilityEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) : RelativeRing root E :=
  if i = 0 then
    if slot = 0 then
      universalCompatibilityCoordinate root src dst e 2
    else -universalCompatibilityCoordinate root src dst e 1
  else if i = 1 then
    if slot = 0 then
      -universalCompatibilityCoordinate root src dst e 2
    else universalCompatibilityCoordinate root src dst e 0
  else
    if slot = 0 then
      universalCompatibilityCoordinate root src dst e 1
    else -universalCompatibilityCoordinate root src dst e 0

/-- Universal triangular identity with the named provenance polynomial on
the right-hand side. -/
theorem universalTriangularResidual_eq_orientedCompatibilityEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    universalTriangularResidual root src dst e i slot =
      universalOrientedCompatibilityEquation root src dst e i slot := by
  rw [universalTriangularResidual,
    triangularResidual_eq_orientedCompatibilityEquation]
  rfl

/-- Sign-free form of the universal triangular identity.  It exposes the
literal compatibility-coordinate provenance selected by the chart. -/
theorem universalTriangularResidual_eq_compatibility_or_neg
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    universalTriangularResidual root src dst e i slot =
        universalCompatibilityCoordinate root src dst e
          (solvingCompatibilityCoordinate i slot) ∨
      universalTriangularResidual root src dst e i slot =
        -universalCompatibilityCoordinate root src dst e
          (solvingCompatibilityCoordinate i slot) := by
  rw [universalTriangularResidual,
    triangularResidual_eq_orientedCompatibilityEquation]
  exact orientedCompatibilityEquation_eq_selected_or_neg
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i slot

/-- The two universal denominator-cleared private-coordinate relations. -/
def universalTriangularResidualIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) : Ideal (RelativeRing root E) :=
  triangularResidualIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- The selected pair of universal compatibility coordinates. -/
def universalCompatibilityPairIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) : Ideal (RelativeRing root E) :=
  compatibilityPairIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- Universal form of the exact two-generator ideal identity. -/
theorem universalTriangularResidualIdeal_eq_compatibilityPairIdeal
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    universalTriangularResidualIdeal root src dst e i =
      universalCompatibilityPairIdeal root src dst e i := by
  exact triangularResidualIdeal_eq_compatibilityPairIdeal
    (universalRelativeTwist root src dst e)
    (universalParameterPin (root := root) e) i

/-- Every universal triangular residual has twist degree one. -/
theorem universalTriangularResidual_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) (slot : Fin 2) :
    (universalTriangularResidual root src dst e i slot).IsHomogeneous 1 := by
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst e i slot with h | h
  · rw [h]
    exact universalCompatibilityCoordinate_isHomogeneous_one
      root src dst e _
  · rw [h]
    exact (universalCompatibilityCoordinate_isHomogeneous_one
      root src dst e _).neg

/-- Incidence semantics: every active realization annihilates both
triangular private-coordinate relations. -/
theorem realChartEvaluation_universalTriangularResidual_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) (i : Fin 3) (slot : Fin 2) :
    realChartEvaluation root p Y
        (universalTriangularResidual root src dst e.1 i slot) = 0 := by
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst e.1 i slot with h | h
  · rw [h]
    exact UniversalHomogeneousChart.IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
      hY root e _
  · rw [h, map_neg,
      UniversalHomogeneousChart.IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
        hY root e _]
    exact neg_zero

end

end PinTriangularElimination

end RB31E2E
