import RB31EndToEnd.Algebra.GroundedTwistPolynomial
import RB31EndToEnd.Incidence.SmallBundleCertificate

/-!
# The universal homogeneous incidence chart

This file separates pin provenance from twist provenance in one nested
polynomial ring.  The pin coordinates live in the coefficient ring

`S = ℚ[PinVariable E]`,

while the outer variables are the six grounded twist coordinates.  Thus the
ordinary grading of the outer polynomial ring is exactly the twist grading:
the Split--Klein null equation has degree two and each pin-compatibility
coordinate has degree one.

The last section supplies the semantic bridge to real incidence
realizations.  It evaluates the pin coefficients at the given placement and
the outer variables at the grounded twist assignment, and proves that all
active null and compatibility equations vanish.  No height, elimination, or
properness conclusion is made here.
-/

namespace RB31E2E

namespace UniversalHomogeneousChart

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial

/-! ## The two provenance layers -/

/-- The inner coefficient ring retaining every pin occurrence and spatial
coordinate. -/
abbrev PinParameterRing (E : Type*) :=
  MvPolynomial (PinVariable E) ℚ

/-- The outer variables are precisely the six coordinates of every
off-root body twist. -/
abbrev GroundedTwistVariable {V : Type*} (root : V) :=
  GroundedColumn root

/-- The relative coordinate ring `S[τ]`: pin parameters are coefficients,
and only the grounded twist variables contribute to its standard grading. -/
abbrev RelativeRing {V : Type*} (root : V) (E : Type*) :=
  MvPolynomial (GroundedTwistVariable root) (PinParameterRing E)

/-! ## Universal pins and grounded twists -/

/-- One universal off-root twist in the outer variables. -/
def universalOffRootTwist {V E : Type*} {root : V}
    (w : OffRoot root) : Twist (RelativeRing root E) :=
  ⟨fun i ↦ X ⟨w, ⟨false, i⟩⟩,
    fun i ↦ X ⟨w, ⟨true, i⟩⟩⟩

/-- The universal grounded twist: the root is zero and every other body has
its own six outer variables. -/
def universalGroundedTwist {V E : Type*} [DecidableEq V] (root : V) :
    V → Twist (RelativeRing root E) :=
  extendOffRoot root (fun w ↦ universalOffRootTwist (E := E) w)

/-- A pin is a coefficient-valued vector in the outer polynomial ring. -/
def universalParameterPin {V E : Type*} {root : V} (e : E) :
    Vec3 (RelativeRing root E) :=
  fun i ↦ C (X ⟨e, i⟩)

/-- The relative universal twist belonging to one oriented occurrence. -/
def universalRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (RelativeRing root E) :=
  universalGroundedTwist (E := E) root (src e) -
    universalGroundedTwist (E := E) root (dst e)

/-- The quadratic Split--Klein equation forced by a stationary pin. -/
def universalNullEquation {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : RelativeRing root E :=
  Twist.splitKlein (universalRelativeTwist root src dst e)

/-- One of the three linear pin-compatibility coordinates. -/
def universalCompatibilityCoordinate {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (j : Fin 3) :
    RelativeRing root E :=
  Twist.eval (universalRelativeTwist root src dst e)
      (universalParameterPin (root := root) e) j

/-! ## Homogeneity in the outer twist grading -/

theorem universalGroundedTwist_angular_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root v : V) (i : Fin 3) :
    ((universalGroundedTwist (E := E) root v).1 i).IsHomogeneous 1 := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot,
      MvPolynomial.isHomogeneous_zero]
  · simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot, hv,
      universalOffRootTwist, MvPolynomial.isHomogeneous_X]

theorem universalGroundedTwist_translational_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root v : V) (i : Fin 3) :
    ((universalGroundedTwist (E := E) root v).2 i).IsHomogeneous 1 := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot,
      MvPolynomial.isHomogeneous_zero]
  · simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot, hv,
      universalOffRootTwist, MvPolynomial.isHomogeneous_X]

theorem universalRelativeTwist_angular_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    ((universalRelativeTwist root src dst e).1 i).IsHomogeneous 1 := by
  exact (universalGroundedTwist_angular_isHomogeneous_one
      (E := E) root (src e) i).sub
    (universalGroundedTwist_angular_isHomogeneous_one
      (E := E) root (dst e) i)

theorem universalRelativeTwist_translational_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    ((universalRelativeTwist root src dst e).2 i).IsHomogeneous 1 := by
  exact (universalGroundedTwist_translational_isHomogeneous_one
      (E := E) root (src e) i).sub
    (universalGroundedTwist_translational_isHomogeneous_one
      (E := E) root (dst e) i)

private theorem universalNullTerm_isHomogeneous_two
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i : Fin 3) :
    (((universalRelativeTwist root src dst e).1 i) *
      ((universalRelativeTwist root src dst e).2 i)).IsHomogeneous 2 := by
  simpa using
    (universalRelativeTwist_angular_isHomogeneous_one root src dst e i).mul
      (universalRelativeTwist_translational_isHomogeneous_one
        root src dst e i)

/-- The universal null equation is homogeneous of twist degree two. -/
theorem universalNullEquation_isHomogeneous_two
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) :
    (universalNullEquation root src dst e).IsHomogeneous 2 := by
  simp only [universalNullEquation, Twist.splitKlein, Vec3.dot]
  simpa using MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i ↦
      ((universalRelativeTwist root src dst e).1 i) *
        ((universalRelativeTwist root src dst e).2 i))
    2 (fun i _ ↦
      universalNullTerm_isHomogeneous_two root src dst e i)

private theorem universalCrossTerm_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (i j : Fin 3) :
    (((universalRelativeTwist root src dst e).1 i) *
      universalParameterPin (root := root) e j).IsHomogeneous 1 := by
  simpa using
    (universalRelativeTwist_angular_isHomogeneous_one root src dst e i).mul
      (MvPolynomial.isHomogeneous_C (GroundedTwistVariable root)
        (X (⟨e, j⟩ : PinVariable E) : PinParameterRing E))

/-- Every compatibility coordinate is homogeneous of twist degree one.
The pin coordinates have degree zero because they belong to the coefficient
ring. -/
theorem universalCompatibilityCoordinate_isHomogeneous_one
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (e : E) (j : Fin 3) :
    (universalCompatibilityCoordinate root src dst e j).IsHomogeneous 1 := by
  fin_cases j
  all_goals
    simp only [universalCompatibilityCoordinate, Twist.eval, Vec3.cross,
      Pi.add_apply]
    apply (universalRelativeTwist_translational_isHomogeneous_one
      root src dst e _).add
    apply (universalCrossTerm_isHomogeneous_one root src dst e _ _).sub
      (universalCrossTerm_isHomogeneous_one root src dst e _ _)

/-! ## Evaluation at a real incidence realization -/

/-- Specialize the inner pin-parameter ring at a real placement. -/
def pinParameterEvaluation {E : Type*} (p : E → Vec3 ℝ) :
    PinParameterRing E →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (assignmentOfPins p)

/-- Assign each outer variable the corresponding coordinate of the grounded
real twist `Y(w) - Y(root)`. -/
def groundedTwistAssignment {V : Type*} (root : V) (Y : V → Twist ℝ) :
    GroundedTwistVariable root → ℝ :=
  fun c ↦ twistCoordinates (Y c.1.1 - Y root) c.2

/-- Simultaneously specialize the pin coefficients and grounded twist
variables. -/
def realChartEvaluation {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    RelativeRing root E →+* ℝ :=
  MvPolynomial.eval₂Hom (pinParameterEvaluation p)
    (groundedTwistAssignment root Y)

@[simp]
theorem pinParameterEvaluation_X {E : Type*} (p : E → Vec3 ℝ)
    (e : E) (i : Fin 3) :
    pinParameterEvaluation p (X (⟨e, i⟩ : PinVariable E)) = p e i := by
  simp [pinParameterEvaluation, assignmentOfPins]

@[simp]
theorem realChartEvaluation_X {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (c : GroundedTwistVariable root) :
    realChartEvaluation root p Y (X c) =
      twistCoordinates (Y c.1.1 - Y root) c.2 := by
  simp [realChartEvaluation, groundedTwistAssignment]

@[simp]
theorem realChartEvaluation_pinCoefficient {V E : Type*} (root : V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ)
    (e : E) (i : Fin 3) :
    realChartEvaluation root p Y
        (C (X (⟨e, i⟩ : PinVariable E))) = p e i := by
  simp [realChartEvaluation]

/-- The universal coefficient-valued pin specializes to the actual pin. -/
theorem map_universalParameterPin {V E : Type*} {root : V}
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) :
    mapVec3 (realChartEvaluation root p Y)
        (universalParameterPin (root := root) e) = p e := by
  funext i
  simp [mapVec3, universalParameterPin]

/-- The universal grounded twist specializes exactly to grounding by
subtraction at `root`. -/
theorem map_universalGroundedTwist {V E : Type*} [DecidableEq V]
    (root v : V) (p : E → Vec3 ℝ) (Y : V → Twist ℝ) :
    mapTwist (realChartEvaluation root p Y)
        (universalGroundedTwist (E := E) root v) = Y v - Y root := by
  by_cases hv : v = root
  · subst v
    simp [universalGroundedTwist,
      GroundedTwistPolynomial.extendOffRoot]
  · apply Prod.ext <;> funext i
    · simp [mapTwist, mapVec3, universalGroundedTwist,
        GroundedTwistPolynomial.extendOffRoot, hv,
        universalOffRootTwist]
    · simp [mapTwist, mapVec3, universalGroundedTwist,
        GroundedTwistPolynomial.extendOffRoot, hv,
        universalOffRootTwist]

/-- Relative universal twists specialize without retaining the arbitrary
grounding body. -/
theorem map_universalRelativeTwist {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (p : E → Vec3 ℝ)
    (Y : V → Twist ℝ) (e : E) :
    mapTwist (realChartEvaluation root p Y)
        (universalRelativeTwist root src dst e) =
      Y (src e) - Y (dst e) := by
  rw [universalRelativeTwist, mapTwist_sub,
    map_universalGroundedTwist, map_universalGroundedTwist]
  module

private theorem map_splitKlein
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Z : Twist R) :
    f (Twist.splitKlein Z) = Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- Evaluation of a universal compatibility coordinate is exactly the
corresponding coordinate of the concrete relative pin velocity. -/
theorem realChartEvaluation_universalCompatibilityCoordinate
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) (j : Fin 3) :
    realChartEvaluation root p Y
        (universalCompatibilityCoordinate root src dst e j) =
      Twist.eval (Y (src e) - Y (dst e)) (p e) j := by
  have h := congrFun
    (mapVec3_eval (realChartEvaluation root p Y)
      (universalRelativeTwist root src dst e)
      (universalParameterPin (root := root) e)) j
  simpa [universalCompatibilityCoordinate, mapVec3,
    map_universalRelativeTwist, map_universalParameterPin] using h

/-- Evaluation of the universal null equation is the concrete
Split--Klein value of the relative twist. -/
theorem realChartEvaluation_universalNullEquation
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) (e : E) :
    realChartEvaluation root p Y (universalNullEquation root src dst e) =
      Twist.splitKlein (Y (src e) - Y (dst e)) := by
  rw [universalNullEquation, map_splitKlein,
    map_universalRelativeTwist]

/-- Every selected incidence occurrence annihilates all three universal
compatibility coordinates. -/
theorem IsIncidenceRealization.realChartEvaluation_compatibility_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) (j : Fin 3) :
    realChartEvaluation root p Y
        (universalCompatibilityCoordinate root src dst e.1 j) = 0 := by
  rw [realChartEvaluation_universalCompatibilityCoordinate]
  exact congrFun (hY.2 e) j

/-- Every selected incidence occurrence annihilates its universal quadratic
null equation. -/
theorem IsIncidenceRealization.realChartEvaluation_null_eq_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : SparseNullIncidence.IsIncidenceRealization src dst active p Y)
    (root : V) (e : active) :
    realChartEvaluation root p Y
        (universalNullEquation root src dst e.1) = 0 := by
  rw [realChartEvaluation_universalNullEquation]
  exact Twist.splitKlein_eq_zero_of_eval_eq_zero
    (Y (src e.1) - Y (dst e.1)) (p e.1) (hY.2 e)

end

end UniversalHomogeneousChart

end RB31E2E
