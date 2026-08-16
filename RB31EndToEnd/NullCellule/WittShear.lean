import RB31EndToEnd.Algebra.GroundedTwistPolynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Angular-fixing Witt shears for the Split--Klein form

This file supplies the literal coordinate change used by the direct
selected-null height argument.  A shear fixes the angular half of a twist
and replaces its translational half by `v + ω × s`.  It is an automorphism,
with inverse parameter `-s`, and it preserves the Split--Klein form exactly.

The second half constructs the induced polynomial algebra equivalence on a
provenance-labelled family of twists.  No height, genericity, or
semismallness statement is assumed.
-/

namespace RB31E2E

namespace WittShear

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial

/-! ## The six-dimensional linear shear -/

/-- The angular-fixing skew Witt shear with parameter `s`. -/
def shear {k : Type*} [CommRing k] (s : Vec3 k) (X : Twist k) : Twist k :=
  (X.1, X.2 + Vec3.cross X.1 s)

@[simp]
theorem shear_fst {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    (shear s X).1 = X.1 := rfl

@[simp]
theorem shear_snd {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    (shear s X).2 = X.2 + Vec3.cross X.1 s := rfl

theorem cross_neg_right {k : Type*} [CommRing k]
    (x s : Vec3 k) :
    Vec3.cross x (-s) = -Vec3.cross x s := by
  funext i
  fin_cases i <;> simp [Vec3.cross] <;> ring

theorem cross_sub_right {k : Type*} [CommRing k]
    (x s t : Vec3 k) :
    Vec3.cross x (s - t) = Vec3.cross x s - Vec3.cross x t := by
  funext i
  fin_cases i <;> simp [Vec3.cross] <;> ring

theorem shear_neg_apply_shear {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    shear (-s) (shear s X) = X := by
  apply Prod.ext
  · rfl
  · simp only [shear_snd, shear_fst, cross_neg_right]
    abel

theorem shear_apply_shear_neg {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    shear s (shear (-s) X) = X := by
  simpa only [neg_neg] using shear_neg_apply_shear (-s) X

/-- The shear is additive. -/
theorem shear_add {k : Type*} [CommRing k]
    (s : Vec3 k) (X Y : Twist k) :
    shear s (X + Y) = shear s X + shear s Y := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [shear, Vec3.cross] <;> ring

/-- The shear commutes with differences. -/
theorem shear_sub {k : Type*} [CommRing k]
    (s : Vec3 k) (X Y : Twist k) :
    shear s (X - Y) = shear s X - shear s Y := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [shear, Vec3.cross] <;> ring

/-- If a twist is nonzero, a one-parameter skew shear can make its
translational half nonzero over any infinite field.  The parameter is a
scalar multiple of an explicitly chosen coordinate axis. -/
theorem exists_scalar_shear_snd_ne_zero
    {k : Type*} [Field k] [Infinite k]
    (X : Twist k) (hX : X ≠ 0) :
    ∃ (r : k) (axis : Fin 3),
      (shear (r • GroundedTwistPolynomial.coordinateUnit axis) X).2 ≠ 0 := by
  by_cases hv : X.2 ≠ 0
  · refine ⟨0, 0, ?_⟩
    intro hs
    apply hv
    have hz : Vec3.cross X.1 (0 : Vec3 k) = 0 := by
      funext i
      fin_cases i <;> simp [Vec3.cross]
    change X.2 + Vec3.cross X.1
      (0 • GroundedTwistPolynomial.coordinateUnit 0) = 0 at hs
    simpa only [zero_smul, hz, add_zero] using hs
  have hv0 : X.2 = 0 := not_ne_iff.mp hv
  have hω : X.1 ≠ 0 := by
    intro hω
    apply hX
    apply Prod.ext
    · exact hω
    · exact hv0
  have hcross : ∃ axis : Fin 3,
      Vec3.cross X.1 (GroundedTwistPolynomial.coordinateUnit axis) ≠ 0 := by
    by_contra h
    have hzero : ∀ axis : Fin 3,
        Vec3.cross X.1
          (GroundedTwistPolynomial.coordinateUnit axis) = 0 := by
      intro axis
      exact not_ne_iff.mp (not_exists.mp h axis)
    have h0 : X.1 0 = 0 := by
      have hz := congrFun (hzero 1) 2
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    have h1 : X.1 1 = 0 := by
      have hz := congrFun (hzero 2) 0
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    have h2 : X.1 2 = 0 := by
      have hz := congrFun (hzero 0) 1
      simpa [Vec3.cross, GroundedTwistPolynomial.coordinateUnit] using hz
    apply hω
    funext i
    fin_cases i <;> assumption
  obtain ⟨axis, haxis⟩ := hcross
  exact ⟨1, axis, by
    simpa [shear, hv0, Vec3.cross_smul_left] using haxis⟩

/-! ## One common base-field shear for a finite family -/

/-- The cubic moment curve in the three-dimensional shear-parameter
space. -/
def momentCurve {k : Type*} [CommRing k] (r : k) : Vec3 k :=
  fun i ↦ r ^ (i.val + 1)

/-- Polynomial version of the same moment curve. -/
def polynomialMomentCurve {K : Type*} [CommRing K] :
    Vec3 (Polynomial K) :=
  fun i ↦ Polynomial.X ^ (i.val + 1)

/-- Translational half of a twist sheared by the polynomial moment curve. -/
def polynomialShearSnd {K : Type*} [CommRing K] (Z : Twist K) :
    Vec3 (Polynomial K) :=
  fun i ↦ Polynomial.C (Z.2 i) +
    Vec3.cross (fun j ↦ Polynomial.C (Z.1 j))
      polynomialMomentCurve i

theorem vecHead_eq_apply_zero {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead v = v 0 := rfl

theorem vecHead_tail_eq_apply_one {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl

theorem vecHead_tail_tail_eq_apply_two {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := rfl

theorem eval_polynomialShearSnd
    {K : Type*} [CommRing K] (Z : Twist K) (r : K) (i : Fin 3) :
    Polynomial.eval r (polynomialShearSnd Z i) =
      (shear (momentCurve r) Z).2 i := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    simp [polynomialShearSnd, polynomialMomentCurve, momentCurve,
      shear, Vec3.cross, Fin.isValue, vecHead_eq_apply_zero,
      vecHead_tail_eq_apply_one, vecHead_tail_tail_eq_apply_two]

/-- A nonzero twist gives a nonzero scalar polynomial among the three
coordinates of its moment-curve shear. -/
theorem exists_polynomialShearSnd_ne_zero
    {K : Type*} [Field K] (Z : Twist K) (hZ : Z ≠ 0) :
    ∃ i : Fin 3, polynomialShearSnd Z i ≠ 0 := by
  by_cases hv : Z.2 ≠ 0
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine ⟨i, fun h ↦ hi ?_⟩
    have he := congrArg (Polynomial.eval 0) h
    have hz := eval_polynomialShearSnd Z 0 i
    rw [h] at hz
    simp only [Polynomial.eval_zero] at hz
    have hs : (shear (momentCurve 0) Z).2 = Z.2 := by
      funext j
      rcases j with ⟨j, hj⟩
      interval_cases j <;>
        simp [shear, momentCurve, Vec3.cross, Fin.isValue,
          vecHead_eq_apply_zero, vecHead_tail_eq_apply_one,
          vecHead_tail_tail_eq_apply_two]
    rw [hs] at hz
    exact hz.symm
  have hv0 : Z.2 = 0 := not_ne_iff.mp hv
  have hω : Z.1 ≠ 0 := by
    intro hω
    apply hZ
    exact Prod.ext hω hv0
  by_cases h0 : Z.1 0 ≠ 0
  · refine ⟨2, fun h ↦ h0 ?_⟩
    have hc := congrArg (fun p : Polynomial K ↦ p.coeff 2) h
    simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
      hv0] using hc
  have h0z : Z.1 0 = 0 := not_ne_iff.mp h0
  by_cases h1 : Z.1 1 ≠ 0
  · refine ⟨0, fun h ↦ h1 ?_⟩
    have hc := congrArg (fun p : Polynomial K ↦ p.coeff 3) h
    simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
      hv0] using hc
  have h1z : Z.1 1 = 0 := not_ne_iff.mp h1
  have h2 : Z.1 2 ≠ 0 := by
    intro h2
    apply hω
    funext i
    fin_cases i <;> assumption
  refine ⟨1, fun h ↦ h2 ?_⟩
  have hc := congrArg (fun p : Polynomial K ↦ p.coeff 1) h
  simpa [polynomialShearSnd, polynomialMomentCurve, Vec3.cross,
    hv0, h0z, h1z] using hc

/-- A nonzero polynomial over an extension field is nonzero at some point
coming from the infinite base field. -/
theorem exists_base_eval_ne_zero
    {k K : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ r : k, Polynomial.eval (algebraMap k K r) p ≠ 0 := by
  by_contra h
  push Not at h
  have hinf : Set.Infinite (Set.range (algebraMap k K)) :=
    Set.infinite_range_of_injective (RingHom.injective (algebraMap k K))
  have hzeroSet : Set.range (algebraMap k K) ⊆
      {x : K | Polynomial.eval x p = Polynomial.eval x 0} := by
    rintro _ ⟨r, rfl⟩
    simpa using h r
  have heval : Set.Infinite
      {x : K | Polynomial.eval x p = Polynomial.eval x 0} :=
    hinf.mono hzeroSet
  exact hp (Polynomial.eq_of_infinite_eval_eq p 0 heval)

/-- A finite family of nonzero twists over an extension field admits one
common shear whose parameter lies in the infinite base field and whose
translational half is nonzero for every member. -/
theorem exists_common_base_shear_snd_ne_zero
    {k K I : Type*} [Field k] [Infinite k]
    [Field K] [Algebra k K] [Fintype I]
    (Z : I → Twist K) (hZ : ∀ i, Z i ≠ 0) :
    ∃ s : Vec3 k, ∀ i,
      (shear (fun j ↦ algebraMap k K (s j)) (Z i)).2 ≠ 0 := by
  classical
  choose c hc using fun i ↦ exists_polynomialShearSnd_ne_zero (Z i) (hZ i)
  let q : I → Polynomial K := fun i ↦ polynomialShearSnd (Z i) (c i)
  have hq (i : I) : q i ≠ 0 := hc i
  let Q : Polynomial K := ∏ i : I, q i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hq i
  obtain ⟨r, hr⟩ := exists_base_eval_ne_zero (k := k) Q hQ
  refine ⟨momentCurve r, fun i hi ↦ ?_⟩
  apply hr
  dsimp [Q]
  change (Polynomial.evalRingHom (algebraMap k K r))
      (∏ i : I, q i) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hcoord := congrFun hi (c i)
  have hs : (fun j ↦ algebraMap k K (momentCurve r j)) =
      momentCurve (algebraMap k K r) := by
    funext j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [momentCurve, map_pow]
  rw [hs] at hcoord
  rw [← eval_polynomialShearSnd (Z i) (algebraMap k K r) (c i)] at hcoord
  simpa [q] using hcoord

/-- A skew Witt shear preserves the Split--Klein quadratic form literally. -/
@[simp]
theorem splitKlein_shear {k : Type*} [CommRing k]
    (s : Vec3 k) (X : Twist k) :
    Twist.splitKlein (shear s X) = Twist.splitKlein X := by
  simp only [Twist.splitKlein, shear_fst, shear_snd, Vec3.dot,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  change Twist.splitKlein X + Vec3.dot X.1 (Vec3.cross X.1 s) =
    Twist.splitKlein X
  rw [Vec3.dot_cross_self_left, add_zero]

/-! ## The induced polynomial algebra equivalence -/

/-- Six coordinate variables for each provenance label. -/
abbrev Variable (U : Type*) := U × TwistCoordinate

/-- The universal twist carried by one label. -/
def universalTwist {k U : Type*} [CommRing k] (u : U) :
    Twist (MvPolynomial (Variable U) k) :=
  (λ i ↦ X ⟨u, ⟨false, i⟩⟩, λ i ↦ X ⟨u, ⟨true, i⟩⟩)

/-- Coordinate assignment defining the polynomial Witt shear. -/
def coordinateImage {k U : Type*} [CommRing k]
    (s : Vec3 k) : Variable U → MvPolynomial (Variable U) k
  | ⟨u, false, i⟩ => X ⟨u, ⟨false, i⟩⟩
  | ⟨u, true, i⟩ =>
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i

/-- Polynomial endomorphism induced by the Witt shear. -/
def hom {k U : Type*} [CommRing k] (s : Vec3 k) :
    MvPolynomial (Variable U) k →ₐ[k] MvPolynomial (Variable U) k :=
  MvPolynomial.aeval (coordinateImage s)

@[simp]
theorem hom_angular_X {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) (i : Fin 3) :
    hom s (X ⟨u, ⟨false, i⟩⟩) = X ⟨u, ⟨false, i⟩⟩ := by
  simp [hom, coordinateImage]

@[simp]
theorem hom_translational_X {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) (i : Fin 3) :
    hom s (X ⟨u, ⟨true, i⟩⟩) =
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i := by
  simp [hom, coordinateImage]

theorem map_cross_universal_angular
    {k U : Type*} [CommRing k]
    (s t : Vec3 k) (u : U) (i : Fin 3) :
    hom s
        ((Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (t j))) i) =
      (Vec3.cross (universalTwist (k := k) u).1
        (fun j ↦ C (t j))) i := by
  fin_cases i <;>
    simp [hom, coordinateImage, universalTwist, Vec3.cross]

theorem hom_comp_neg {k U : Type*} [CommRing k] (s : Vec3 k) :
    (hom (U := U) s).comp (hom (U := U) (-s)) =
      AlgHom.id k (MvPolynomial (Variable U) k) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨u, ⟨b, i⟩⟩
  cases b
  · simp
  · rw [AlgHom.comp_apply, hom_translational_X, map_add,
      hom_translational_X, map_cross_universal_angular]
    rw [show (fun j ↦ C ((-s) j)) =
        -(fun j ↦ C (s j)) by funext j; simp]
    rw [cross_neg_right]
    simp only [Pi.neg_apply]
    simp

theorem hom_neg_comp {k U : Type*} [CommRing k] (s : Vec3 k) :
    (hom (U := U) (-s)).comp (hom (U := U) s) =
      AlgHom.id k (MvPolynomial (Variable U) k) := by
  simpa only [neg_neg] using hom_comp_neg (U := U) (-s)

/-- The polynomial algebra automorphism induced by a Witt shear. -/
def algEquiv {k U : Type*} [CommRing k] (s : Vec3 k) :
    MvPolynomial (Variable U) k ≃ₐ[k] MvPolynomial (Variable U) k :=
  AlgEquiv.ofAlgHom (hom s) (hom (-s))
    (hom_comp_neg s) (hom_neg_comp s)

@[simp]
theorem algEquiv_apply {k U : Type*} [CommRing k]
    (s : Vec3 k) (f : MvPolynomial (Variable U) k) :
    algEquiv s f = hom s f := rfl

theorem map_universalTwist {k U : Type*} [CommRing k]
    (s : Vec3 k) (u : U) :
    mapTwist (algEquiv s).toRingEquiv.toRingHom
        (universalTwist (k := k) u) =
      shear (fun j ↦ C (s j)) (universalTwist (k := k) u) := by
  apply Prod.ext <;> funext i
  · change algEquiv s (X ⟨u, ⟨false, i⟩⟩) = X ⟨u, ⟨false, i⟩⟩
    exact hom_angular_X s u i
  · change algEquiv s (X ⟨u, ⟨true, i⟩⟩) =
      X ⟨u, ⟨true, i⟩⟩ +
        (Vec3.cross (universalTwist (k := k) u).1
          (fun j ↦ C (s j))) i
    exact hom_translational_X s u i

theorem map_splitKlein {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) :
    f (Twist.splitKlein Z) = Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- Every labelled Split--Klein difference polynomial is fixed. -/
theorem algEquiv_splitKlein_sub {k U : Type*} [CommRing k]
    (s : Vec3 k) (u v : U) :
    algEquiv s
        (Twist.splitKlein
          (universalTwist (k := k) u - universalTwist (k := k) v)) =
      Twist.splitKlein
        (universalTwist (k := k) u - universalTwist (k := k) v) := by
  rw [algEquiv_apply]
  have hmap : mapTwist (hom s).toRingHom
      (universalTwist (k := k) u - universalTwist (k := k) v) =
      shear (fun j ↦ C (s j))
        (universalTwist (k := k) u - universalTwist (k := k) v) := by
    rw [mapTwist_sub]
    rw [show mapTwist (hom s).toRingHom (universalTwist (k := k) u) =
        shear (fun j ↦ C (s j)) (universalTwist (k := k) u) by
          simpa using map_universalTwist s u]
    rw [show mapTwist (hom s).toRingHom (universalTwist (k := k) v) =
        shear (fun j ↦ C (s j)) (universalTwist (k := k) v) by
          simpa using map_universalTwist s v]
    rw [← shear_sub]
  change (hom s).toRingHom
      (Twist.splitKlein
        (universalTwist (k := k) u - universalTwist (k := k) v)) = _
  rw [map_splitKlein, hmap, splitKlein_shear]

end

end WittShear

end RB31E2E
