import RB31EndToEnd.Algebra.ComplexRealSpecialization
import RB31EndToEnd.Algebra.GroundedTwist

/-!
# The provenance polynomial matrix of the grounded twist operator

For a fixed grounded body, this file writes the actual pin operator as an
integer-coefficient polynomial matrix.  Its variables retain the pin
occurrence and spatial coordinate as provenance labels.  The comparison with
`groundedPinOperator` is an equality after explicit coordinate linear
equivalences, not merely an equality of ranks.
-/

namespace RB31E2E

namespace GroundedTwistPolynomial

noncomputable section

open MvPolynomial

/-- One variable for every coordinate of every pin occurrence. -/
abbrev PinVariable (E : Type*) := E × Fin 3

/-- Rows are pin occurrences together with output-velocity coordinates. -/
abbrev GroundedRow (E : Type*) := E × Fin 3

/-- `false` labels angular and `true` translational twist coordinates. -/
abbrev TwistCoordinate := Bool × Fin 3

/-- Columns are provenance-labelled coordinates of bodies other than root. -/
abbrev GroundedColumn {W : Type*} (root : W) := OffRoot root × TwistCoordinate

/-- Explicit coordinates on one six-dimensional twist. -/
def twistCoordinates {k : Type*} [Field k] :
    Twist k ≃ₗ[k] (TwistCoordinate → k) where
  toFun X
    | ⟨false, i⟩ => X.1 i
    | ⟨true, i⟩ => X.2 i
  invFun x :=
    ⟨fun i ↦ x ⟨false, i⟩, fun i ↦ x ⟨true, i⟩⟩
  left_inv X := by
    apply Prod.ext <;> funext i <;> rfl
  right_inv x := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl
  map_add' X Y := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl
  map_smul' a X := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl

@[simp] theorem twistCoordinates_angular {k : Type*} [Field k]
    (X : Twist k) (i : Fin 3) :
    twistCoordinates X ⟨false, i⟩ = X.1 i := rfl

@[simp] theorem twistCoordinates_translational {k : Type*} [Field k]
    (X : Twist k) (i : Fin 3) :
    twistCoordinates X ⟨true, i⟩ = X.2 i := rfl

/-- Coordinates on all off-root twists, with body labels retained. -/
def groundedTwistCoordinates {k W : Type*} [Field k] (root : W) :
    (OffRoot root → Twist k) ≃ₗ[k] (GroundedColumn root → k) :=
  (LinearEquiv.piCongrRight
      (fun _ : OffRoot root ↦ twistCoordinates (k := k))).trans
    (LinearEquiv.curry k k (OffRoot root) TwistCoordinate).symm

@[simp] theorem groundedTwistCoordinates_apply
    {k W : Type*} [Field k] (root : W)
    (X : OffRoot root → Twist k) (c : GroundedColumn root) :
    groundedTwistCoordinates root X c = twistCoordinates (X c.1) c.2 :=
  rfl

/-- Coordinates on all pin-velocity outputs. -/
def pinVelocityCoordinates {k E : Type*} [Field k] :
    (E → Vec3 k) ≃ₗ[k] (GroundedRow E → k) :=
  (LinearEquiv.curry k k E (Fin 3)).symm

@[simp] theorem pinVelocityCoordinates_apply
    {k E : Type*} [Field k] (Y : E → Vec3 k) (r : GroundedRow E) :
    pinVelocityCoordinates Y r = Y r.1 r.2 := rfl

/-- Recover pins from one assignment of the provenance variables. -/
def pinsOfAssignment {k E : Type*} (z : PinVariable E → k) : E → Vec3 k :=
  fun e i ↦ z ⟨e, i⟩

/-- Encode concrete pins as an assignment of all provenance variables. -/
def assignmentOfPins {k E : Type*} (p : E → Vec3 k) : PinVariable E → k :=
  fun ei ↦ p ei.1 ei.2

@[simp] theorem pinsOfAssignment_assignmentOfPins
    {k E : Type*} (p : E → Vec3 k) :
    pinsOfAssignment (assignmentOfPins p) = p := by
  rfl

@[simp] theorem assignmentOfPins_pinsOfAssignment
    {k E : Type*} (z : PinVariable E → k) :
    assignmentOfPins (pinsOfAssignment z) = z := by
  rfl

/-- A coordinate unit vector over any coefficient ring. -/
def coordinateUnit {R : Type*} [CommRing R] (i : Fin 3) : Vec3 R :=
  fun j ↦ if j = i then 1 else 0

/-- The angular/translational unit twist indexed by one column coordinate. -/
def twistCoordinateUnit {R : Type*} [CommRing R]
    (c : TwistCoordinate) : Twist R :=
  match c.1 with
  | false => ⟨coordinateUnit c.2, 0⟩
  | true => ⟨0, coordinateUnit c.2⟩

/-- The off-root coordinate basis vector indexed by a matrix column. -/
def groundedCoordinateUnit {R W : Type*} [CommRing R] [DecidableEq W]
    {root : W} (c : GroundedColumn root) : OffRoot root → Twist R :=
  fun w ↦ if w = c.1 then twistCoordinateUnit c.2 else 0

/-- Extend an off-root assignment by zero, over a general commutative ring. -/
def extendOffRoot {R W : Type*} [CommRing R] [DecidableEq W]
    (root : W) (X : OffRoot root → Twist R) : W → Twist R :=
  fun w ↦ if h : w = root then 0 else X ⟨w, h⟩

theorem extendOffRoot_eq_extendGrounded
    {k W : Type*} [Field k] [DecidableEq W]
    (root : W) (X : OffRoot root → Twist k) :
    extendOffRoot root X = extendGrounded root X := by
  rfl

/-- The universal provenance-labelled pin. -/
def universalPin {E : Type*} (e : E) :
    Vec3 (MvPolynomial (PinVariable E) ℤ) :=
  fun i ↦ X ⟨e, i⟩

/-- The same explicit coordinate matrix over any commutative coefficient
ring, for a concrete pin assignment. -/
def groundedPinMatrix {R W E : Type*} [CommRing R] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 R) :
    Matrix (GroundedRow E) (GroundedColumn root) R :=
  fun r c ↦
    Twist.eval
      (extendOffRoot root (groundedCoordinateUnit c) (src r.1) -
        extendOffRoot root (groundedCoordinateUnit c) (dst r.1))
      (p r.1) r.2

/-- The integer-coefficient, provenance-labelled polynomial matrix of the
grounded pin operator. -/
def groundedPinPolynomialMatrix {W E : Type*} [DecidableEq W]
    (root : W) (src dst : E → W) :
    Matrix (GroundedRow E) (GroundedColumn root)
      (MvPolynomial (PinVariable E) ℤ) :=
  groundedPinMatrix root src dst universalPin

private theorem totalDegree_extend_coordinateUnit_fst
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (w : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
        (groundedCoordinateUnit
          (R := MvPolynomial σ ℤ) c) w).1 i) = 0 := by
  rcases c with ⟨body, ⟨b, j⟩⟩
  cases b <;>
    simp [extendOffRoot, groundedCoordinateUnit, twistCoordinateUnit] <;>
    split_ifs
  all_goals
    by_cases hij : i = j <;>
      simp [coordinateUnit, hij]

private theorem totalDegree_extend_coordinateUnit_snd
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (w : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
        (groundedCoordinateUnit
          (R := MvPolynomial σ ℤ) c) w).2 i) = 0 := by
  rcases c with ⟨body, ⟨b, j⟩⟩
  cases b <;>
    simp [extendOffRoot, groundedCoordinateUnit, twistCoordinateUnit] <;>
    split_ifs
  all_goals
    by_cases hij : i = j <;>
      simp [coordinateUnit, hij]

private theorem totalDegree_groundedDifference_fst_le_zero
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (u v : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) u -
        extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) v).1 i) ≤ 0 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  rw [totalDegree_extend_coordinateUnit_fst,
    totalDegree_extend_coordinateUnit_fst]
  simp

private theorem totalDegree_groundedDifference_snd_le_zero
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (u v : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) u -
        extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) v).2 i) ≤ 0 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  rw [totalDegree_extend_coordinateUnit_snd,
    totalDegree_extend_coordinateUnit_snd]
  simp

private theorem totalDegree_constant_mul_X_le_one
    {σ : Type*} (P : MvPolynomial σ ℤ) (v : σ)
    (hP : P.totalDegree ≤ 0) :
    (P * X v).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_X]
  omega

private theorem totalDegree_cross_universalPin_le_one
    {E : Type*} (omega : Vec3 (MvPolynomial (PinVariable E) ℤ))
    (e : E) (j : Fin 3)
    (homega : ∀ i, (omega i).totalDegree ≤ 0) :
    (Vec3.cross omega (universalPin e) j).totalDegree ≤ 1 := by
  fin_cases j <;>
    simp only [Vec3.cross, universalPin] <;>
    apply (MvPolynomial.totalDegree_sub _ _).trans <;>
    apply Nat.max_le.mpr <;>
    constructor <;>
    apply totalDegree_constant_mul_X_le_one <;>
    exact homega _

/-- Every entry of the provenance matrix has total degree at most one.  Thus
translation columns are constant and angular columns are linear in the pin
coordinates; no higher-degree coefficient is hidden in the construction. -/
theorem groundedPinPolynomialMatrix_totalDegree_le_one
    {W E : Type*} [DecidableEq W]
    (root : W) (src dst : E → W)
    (r : GroundedRow E) (c : GroundedColumn root) :
    MvPolynomial.totalDegree
      (groundedPinPolynomialMatrix root src dst r c) ≤ 1 := by
  rcases r with ⟨e, j⟩
  let D : Twist (MvPolynomial (PinVariable E) ℤ) :=
    extendOffRoot root (groundedCoordinateUnit c) (src e) -
      extendOffRoot root (groundedCoordinateUnit c) (dst e)
  have hω (i : Fin 3) : (D.1 i).totalDegree ≤ 0 := by
    exact totalDegree_groundedDifference_fst_le_zero
      root c (src e) (dst e) i
  have hv (i : Fin 3) : (D.2 i).totalDegree ≤ 0 := by
    exact totalDegree_groundedDifference_snd_le_zero
      root c (src e) (dst e) i
  change MvPolynomial.totalDegree
    (D.2 j + Vec3.cross D.1 (universalPin e) j) ≤ 1
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply Nat.max_le.mpr
  exact ⟨(hv j).trans (by omega),
    totalDegree_cross_universalPin_le_one D.1 e j hω⟩

/-! ## Equality with the actual grounded operator -/

/-- The coordinate basis on the off-root twist space. -/
def groundedTwistBasis {k W : Type*} [Field k] [Fintype W]
    [DecidableEq W] (root : W) :
    Module.Basis (GroundedColumn root) k (OffRoot root → Twist k) :=
  Module.Basis.ofEquivFun (groundedTwistCoordinates root)

/-- The coordinate basis on the pin-velocity output space. -/
def pinVelocityBasis {k E : Type*} [Field k] [Fintype E] :
    Module.Basis (GroundedRow E) k (E → Vec3 k) :=
  Module.Basis.ofEquivFun pinVelocityCoordinates

theorem groundedTwistBasis_apply_eq_coordinateUnit
    {k W : Type*} [Field k] [Fintype W] [DecidableEq W]
    (root : W) (c : GroundedColumn root) :
    groundedTwistBasis (k := k) root c = groundedCoordinateUnit c := by
  rw [groundedTwistBasis, Module.Basis.coe_ofEquivFun]
  apply (groundedTwistCoordinates (k := k) root).injective
  funext d
  rw [LinearEquiv.apply_symm_apply]
  rcases c with ⟨w, ⟨bc, i⟩⟩
  rcases d with ⟨v, ⟨bd, j⟩⟩
  cases bc <;> cases bd <;>
    by_cases hwv : v = w <;>
    by_cases hij : j = i <;>
    simp [groundedCoordinateUnit, twistCoordinateUnit, coordinateUnit,
      Pi.single_apply, Prod.ext_iff, hwv, hij]

/-- The usual coordinate matrix of the actual `groundedPinOperator`. -/
def groundedPinCoordinateMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Matrix (GroundedRow E) (GroundedColumn root) k :=
  LinearMap.toMatrix (groundedTwistBasis root) pinVelocityBasis
    (groundedPinOperator root src dst p)

/-- Entrywise equality between the explicit matrix and the coordinate matrix
of the genuine grounded operator. -/
theorem groundedPinMatrix_eq_coordinateMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    groundedPinMatrix root src dst p =
      groundedPinCoordinateMatrix root src dst p := by
  ext r c
  rw [groundedPinCoordinateMatrix, LinearMap.toMatrix_apply,
    groundedTwistBasis_apply_eq_coordinateUnit]
  change groundedPinMatrix root src dst p r c =
    pinVelocityCoordinates
      (groundedPinOperator root src dst p (groundedCoordinateUnit c)) r
  simp only [pinVelocityCoordinates_apply, groundedPinOperator_apply]
  rfl

/-- Matrix multiplication is literally the grounded operator after the two
displayed coordinate equivalences. -/
theorem groundedPinMatrix_mulVec_coordinates
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k)
    (Y : OffRoot root → Twist k) :
    (groundedPinMatrix root src dst p).mulVec
        (groundedTwistCoordinates root Y) =
      pinVelocityCoordinates (groundedPinOperator root src dst p Y) := by
  rw [groundedPinMatrix_eq_coordinateMatrix]
  simpa [groundedPinCoordinateMatrix, groundedTwistBasis, pinVelocityBasis]
    using (groundedPinOperator root src dst p).toMatrix_mulVec_repr
      (groundedTwistBasis root) pinVelocityBasis Y

/-- Injectivity of the explicit coordinate matrix is equivalent to
injectivity of the genuine grounded operator. -/
theorem groundedPinMatrix_mulVec_injective_iff
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Function.Injective (groundedPinMatrix root src dst p).mulVec ↔
      Function.Injective (groundedPinOperator root src dst p) := by
  constructor
  · intro hMatrix Y Z hYZ
    apply (groundedTwistCoordinates (k := k) root).injective
    apply hMatrix
    rw [groundedPinMatrix_mulVec_coordinates,
      groundedPinMatrix_mulVec_coordinates, hYZ]
  · intro hOperator u v huv
    obtain ⟨Y, rfl⟩ := (groundedTwistCoordinates (k := k) root).surjective u
    obtain ⟨Z, rfl⟩ := (groundedTwistCoordinates (k := k) root).surjective v
    apply congrArg (groundedTwistCoordinates (k := k) root)
    apply hOperator
    apply (pinVelocityCoordinates (k := k) (E := E)).injective
    simpa only [groundedPinMatrix_mulVec_coordinates] using huv

/-! ## Polynomial specialization -/

/-- Apply a coefficient homomorphism coordinatewise to a three-vector. -/
def mapVec3 {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Vec3 R) : Vec3 S :=
  fun i ↦ f (v i)

/-- Apply a coefficient homomorphism coordinatewise to a twist. -/
def mapTwist {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Y : Twist R) : Twist S :=
  ⟨mapVec3 f Y.1, mapVec3 f Y.2⟩

@[simp] theorem mapTwist_zero
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    mapTwist f (0 : Twist R) = 0 := by
  apply Prod.ext <;> funext i <;> simp [mapTwist, mapVec3]

@[simp] theorem mapTwist_sub
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Y Z : Twist R) :
    mapTwist f (Y - Z) = mapTwist f Y - mapTwist f Z := by
  apply Prod.ext <;> funext i <;> simp [mapTwist, mapVec3]

/-- Rigid-body velocity evaluation commutes with coefficient maps. -/
theorem mapVec3_eval
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Y : Twist R) (p : Vec3 R) :
    mapVec3 f (Twist.eval Y p) =
      Twist.eval (mapTwist f Y) (mapVec3 f p) := by
  funext i
  fin_cases i <;>
    simp [mapVec3, mapTwist, Twist.eval, Vec3.cross]

@[simp] theorem mapTwist_twistCoordinateUnit
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c : TwistCoordinate) :
    mapTwist f (twistCoordinateUnit c : Twist R) =
      (twistCoordinateUnit c : Twist S) := by
  rcases c with ⟨b, i⟩
  cases b <;>
    apply Prod.ext <;>
    funext j <;>
    simp [mapTwist, mapVec3, twistCoordinateUnit, coordinateUnit]

theorem mapTwist_groundedCoordinateUnit
    {R S W : Type*} [CommRing R] [CommRing S] [DecidableEq W]
    (f : R →+* S) {root : W} (c : GroundedColumn root) :
    (fun w ↦ mapTwist f (groundedCoordinateUnit (R := R) c w)) =
      groundedCoordinateUnit (R := S) c := by
  funext w
  by_cases hw : w = c.1 <;>
    simp [groundedCoordinateUnit, hw]

theorem mapTwist_extendOffRoot
    {R S W : Type*} [CommRing R] [CommRing S] [DecidableEq W]
    (f : R →+* S) (root : W) (Y : OffRoot root → Twist R) :
    (fun w ↦ mapTwist f (extendOffRoot root Y w)) =
      extendOffRoot root (fun u ↦ mapTwist f (Y u)) := by
  funext w
  by_cases hw : w = root <;>
    simp [extendOffRoot, hw]

theorem mapVec3_universalPin
    {k E : Type*} [Field k] (z : PinVariable E → k) (e : E) :
    mapVec3 (MvPolynomial.eval₂Hom (Int.castRingHom k) z) (universalPin e) =
      pinsOfAssignment z e := by
  funext i
  simp [mapVec3, universalPin, pinsOfAssignment]

/-- Specializing the provenance matrix gives the explicit matrix at the
corresponding pin placement, entry for entry.  This holds over every field,
and hence in particular over every characteristic-zero field, `ℝ`, and `ℂ`. -/
theorem specialize_groundedPinPolynomialMatrix
    {k W E : Type*} [Field k] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst) =
      groundedPinMatrix root src dst (pinsOfAssignment z) := by
  ext r c
  rcases r with ⟨e, j⟩
  change
    MvPolynomial.eval₂ (Int.castRingHom k) z
      (groundedPinMatrix root src dst universalPin (e, j) c) =
    groundedPinMatrix root src dst (pinsOfAssignment z) (e, j) c
  change
    (mapVec3 (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
      (Twist.eval
        (extendOffRoot root (groundedCoordinateUnit c) (src e) -
          extendOffRoot root (groundedCoordinateUnit c) (dst e))
        (universalPin e))) j = _
  rw [mapVec3_eval, mapTwist_sub]
  rw [show mapTwist (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
        (extendOffRoot root (groundedCoordinateUnit c) (src e)) =
      extendOffRoot root (groundedCoordinateUnit c) (src e) by
    have h := congrFun
      (mapTwist_extendOffRoot
        (MvPolynomial.eval₂Hom (Int.castRingHom k) z) root
        (groundedCoordinateUnit c)) (src e)
    simpa [mapTwist_groundedCoordinateUnit] using h]
  rw [show mapTwist (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
        (extendOffRoot root (groundedCoordinateUnit c) (dst e)) =
      extendOffRoot root (groundedCoordinateUnit c) (dst e) by
    have h := congrFun
      (mapTwist_extendOffRoot
        (MvPolynomial.eval₂Hom (Int.castRingHom k) z) root
        (groundedCoordinateUnit c)) (dst e)
    simpa [mapTwist_groundedCoordinateUnit] using h]
  rw [mapVec3_universalPin]
  rfl

/-- Direct matrix/operator identity: after specialization, the provenance
matrix is exactly `LinearMap.toMatrix` of `groundedPinOperator` in the
displayed bases. -/
theorem specialize_groundedPinPolynomialMatrix_eq_operatorMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst) =
      groundedPinCoordinateMatrix root src dst (pinsOfAssignment z) := by
  rw [specialize_groundedPinPolynomialMatrix,
    groundedPinMatrix_eq_coordinateMatrix]

/-- The fully specialized polynomial matrix acts as the actual grounded pin
operator under the explicit coordinate equivalences. -/
theorem specializedPolynomialMatrix_mulVec_coordinates
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k)
    (Y : OffRoot root → Twist k) :
    (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst)).mulVec
        (groundedTwistCoordinates root Y) =
      pinVelocityCoordinates
        (groundedPinOperator root src dst (pinsOfAssignment z) Y) := by
  rw [specialize_groundedPinPolynomialMatrix]
  exact groundedPinMatrix_mulVec_coordinates root src dst
    (pinsOfAssignment z) Y

/-- The conjugacy as an equality of linear maps, rather than just a pointwise
statement about vectors. -/
theorem specializedPolynomialMatrix_operator_conjugacy
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst)).mulVecLin.comp
        (groundedTwistCoordinates root).toLinearMap =
      (pinVelocityCoordinates (k := k) (E := E)).toLinearMap.comp
        (groundedPinOperator root src dst (pinsOfAssignment z)) := by
  apply LinearMap.ext
  intro Y
  exact specializedPolynomialMatrix_mulVec_coordinates
    root src dst z Y

/-- Specialization is injective exactly when the genuine grounded operator at
the specialized pins is injective. -/
theorem specializedPolynomialMatrix_injective_iff_grounded
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    Function.Injective
        (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
          (groundedPinPolynomialMatrix root src dst)).mulVec ↔
      Function.Injective
        (groundedPinOperator root src dst (pinsOfAssignment z)) := by
  rw [specialize_groundedPinPolynomialMatrix]
  exact groundedPinMatrix_mulVec_injective_iff root src dst
    (pinsOfAssignment z)

/-! ## The complex-to-real rigidity transfer -/

/-- A complex pin placement with injective grounded operator gives a real pin
placement with injective grounded operator.  The fixed `root` is the explicit
witness that the body type is nonempty. -/
theorem exists_real_grounded_injective_of_exists_complex
    {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W)
    (hComplex : ∃ p : E → Vec3 ℂ,
      Function.Injective (groundedPinOperator root src dst p)) :
    ∃ p : E → Vec3 ℝ,
      Function.Injective (groundedPinOperator root src dst p) := by
  obtain ⟨pComplex, hpComplex⟩ := hComplex
  have hMatrixComplex : ∃ z : PinVariable E → ℂ,
      Function.Injective
        (ComplexRealSpecialization.specializeMatrix (Int.castRingHom ℂ) z
          (groundedPinPolynomialMatrix root src dst)).mulVec := by
    refine ⟨assignmentOfPins pComplex, ?_⟩
    apply (specializedPolynomialMatrix_injective_iff_grounded
      root src dst (assignmentOfPins pComplex)).mpr
    simpa using hpComplex
  obtain ⟨zReal, hzReal⟩ :=
    ComplexRealSpecialization.exists_real_specialization_injective_of_complex
      (groundedPinPolynomialMatrix root src dst) hMatrixComplex
  refine ⟨pinsOfAssignment zReal, ?_⟩
  exact (specializedPolynomialMatrix_injective_iff_grounded
    root src dst zReal).mp hzReal

/-- Genuine end-to-end transfer: existence of a complex rigid body-twist pin
placement implies existence of a real rigid body-twist pin placement. -/
theorem exists_real_twistRigidAt_of_exists_complex
    {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W)
    (hComplex : ∃ p : E → Vec3 ℂ, TwistRigidAt src dst p) :
    ∃ p : E → Vec3 ℝ, TwistRigidAt src dst p := by
  have hGroundedComplex : ∃ p : E → Vec3 ℂ,
      Function.Injective (groundedPinOperator root src dst p) := by
    obtain ⟨p, hp⟩ := hComplex
    exact ⟨p,
      (groundedPinOperator_injective_iff_twistRigidAt root src dst p).mpr hp⟩
  obtain ⟨pReal, hpReal⟩ :=
    exists_real_grounded_injective_of_exists_complex
      root src dst hGroundedComplex
  exact ⟨pReal,
    (groundedPinOperator_injective_iff_twistRigidAt
      root src dst pReal).mp hpReal⟩

end

end GroundedTwistPolynomial

end RB31E2E
