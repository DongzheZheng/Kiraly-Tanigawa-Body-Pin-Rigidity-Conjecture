import RB31EndToEnd.Algebra.LinearFormIdeal
import RB31EndToEnd.Incidence.PinOuterActiveHeight
import RB31EndToEnd.Linear.GroundedDirectionConstraint
import RB31EndToEnd.NullCellule.WittShear
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Angular/translational splitting of grounded twists

The grounded six-coordinate polynomial ring is rewritten as a polynomial
ring in angular coordinates over the polynomial ring in translational
coordinates.  A Split--Klein null equation then becomes a literal linear
form in the angular variables, with the ordinary grounded direction row as
its coefficient vector.
-/

namespace RB31E2E

namespace GroundedTwistSplit

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open LinearFormIdeal
open UniversalHomogeneousChart

/-- Three spatial coordinates at every non-root body.  The same label type
is used once in the coefficient layer and once in the outer layer. -/
abbrev SpatialVariable {V : Type*} (root : V) := OffRoot root × Fin 3

/-- Angular variables are the left summand and translational variables are
the right summand. -/
def splitIndexEquiv {V : Type*} (root : V) :
    SpatialVariable root ⊕ SpatialVariable root ≃
      GroundedTwistVariable root where
  toFun
    | Sum.inl x => ⟨x.1, ⟨false, x.2⟩⟩
    | Sum.inr x => ⟨x.1, ⟨true, x.2⟩⟩
  invFun x := if x.2.1 then
      Sum.inr ⟨x.1, x.2.2⟩
    else Sum.inl ⟨x.1, x.2.2⟩
  left_inv x := by
    cases x with
    | inl x => rfl
    | inr x => rfl
  right_inv x := by
    rcases x with ⟨w, ⟨b, i⟩⟩
    cases b <;> rfl

/-- The explicit iterated polynomial presentation
`Q[translational][angular] ≃ Q[angular,translational]`. -/
def splitEquiv {k V : Type*} [CommRing k] (root : V) :
    MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) k) ≃ₐ[k]
      MvPolynomial (GroundedTwistVariable root) k :=
  (MvPolynomial.sumAlgEquiv k
      (SpatialVariable root) (SpatialVariable root)).symm |>.trans
    (MvPolynomial.renameEquiv k (splitIndexEquiv root))

/-- Linear polynomial over an arbitrary commutative coefficient ring.  The
field-specialized version is `LinearFormIdeal.linearPolynomial`. -/
def coefficientLinearPolynomial
    {A I : Type*} [CommRing A] [Fintype I]
    (v : I → A) : MvPolynomial I A :=
  ∑ i, C (v i) * X i

@[simp] theorem splitEquiv_angular_X
    {k V : Type*} [CommRing k] (root : V)
    (x : SpatialVariable root) :
    splitEquiv (k := k) root (X x) =
      X ⟨x.1, ⟨false, x.2⟩⟩ := by
  change MvPolynomial.rename (splitIndexEquiv root)
    (MvPolynomial.iterToSum k (SpatialVariable root)
      (SpatialVariable root) (X x)) = _
  rw [MvPolynomial.iterToSum_X, MvPolynomial.rename_X]
  rfl

@[simp] theorem splitEquiv_translational_C_X
    {k V : Type*} [CommRing k] (root : V)
    (x : SpatialVariable root) :
    splitEquiv (k := k) root (C (X x)) =
      X ⟨x.1, ⟨true, x.2⟩⟩ := by
  change MvPolynomial.rename (splitIndexEquiv root)
    (MvPolynomial.iterToSum k (SpatialVariable root)
      (SpatialVariable root) (C (X x))) = _
  rw [MvPolynomial.iterToSum_C_X, MvPolynomial.rename_X]
  rfl

/-- One universal off-root twist in the iterated presentation. -/
def iteratedOffRootTwist
    {k V : Type*} [CommRing k] {root : V} (w : OffRoot root) :
    Twist (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) k)) :=
  ⟨fun i ↦ X ⟨w, i⟩, fun i ↦ C (X ⟨w, i⟩)⟩

/-- Root-zero universal twists in the iterated presentation. -/
def iteratedGroundedTwist
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Twist (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) k)) :=
  extendOffRoot root (iteratedOffRootTwist (k := k))

theorem map_iteratedOffRootTwist
    {V : Type*} {root : V} (w : OffRoot root) :
    mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom
        (iteratedOffRootTwist (k := ℚ) w) =
      coefficientOffRootTwist w := by
  apply Prod.ext <;> funext i <;> simp [iteratedOffRootTwist,
    coefficientOffRootTwist, mapTwist, mapVec3]

theorem map_iteratedGroundedTwist
    {V : Type*} [DecidableEq V] (root v : V) :
    mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom
        (iteratedGroundedTwist (k := ℚ) root v) =
      coefficientGroundedTwist root v := by
  by_cases hv : v = root
  · subst v
    simp [iteratedGroundedTwist, coefficientGroundedTwist,
      extendOffRoot, mapTwist_zero]
  · unfold iteratedGroundedTwist coefficientGroundedTwist extendOffRoot
    rw [dif_neg hv, dif_neg hv]
    exact map_iteratedOffRootTwist ⟨v, hv⟩

/-- The oriented occurrence direction row, restricted to non-root blocks. -/
def occurrenceDirectionRow
    {k V E : Type*} [CommRing k] [DecidableEq V]
    (root : V) (src dst : E → V) (a : V → Fin 3 → k) (e : E) :
    SpatialVariable root → k :=
  fun x ↦
    (if src e = x.1.1 then a (src e) x.2 - a (dst e) x.2 else 0) +
      (if dst e = x.1.1 then -(a (src e) x.2 - a (dst e) x.2) else 0)

/-- Universal translational placement in the coefficient polynomial ring. -/
def coefficientPlacement
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Fin 3 → MvPolynomial (SpatialVariable root) k :=
  fun v i ↦ if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩

theorem coefficientPlacement_root
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    coefficientPlacement (k := k) root root = 0 := by
  funext i
  simp [coefficientPlacement]

theorem iteratedGroundedTwist_fst
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) (i : Fin 3) :
    (iteratedGroundedTwist (k := k) root v).1 i =
      if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩ := by
  by_cases hv : v = root <;>
    simp [iteratedGroundedTwist, iteratedOffRootTwist,
      extendOffRoot, hv]

theorem iteratedGroundedTwist_snd
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) (i : Fin 3) :
    (iteratedGroundedTwist (k := k) root v).2 i =
      C (coefficientPlacement (k := k) root v i) := by
  by_cases hv : v = root <;>
    simp [iteratedGroundedTwist, iteratedOffRootTwist,
      coefficientPlacement, extendOffRoot, hv]

/-- Universal angular coordinate, with the grounded body set to zero. -/
def angularCoordinate
    {k V : Type*} [CommRing k] [DecidableEq V] (root : V) :
    V → Fin 3 →
      MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) k) :=
  fun v i ↦ if h : v = root then 0 else X ⟨⟨v, h⟩, i⟩

theorem iteratedGroundedTwist_fst_eq_angularCoordinate
    {k V : Type*} [CommRing k] [DecidableEq V] (root v : V) :
    (iteratedGroundedTwist (k := k) root v).1 =
      angularCoordinate (k := k) root v := by
  funext i
  exact iteratedGroundedTwist_fst root v i

/-- A finite sum over the off-root subtype selects the unique term whose
underlying body is a prescribed non-root body. -/
theorem sum_X_C_if_eq_offRoot
    {k V : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root v : V) (hv : v ≠ root) (j : Fin 3)
    (q : MvPolynomial (SpatialVariable root) k) :
    ∑ w : OffRoot root,
        (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if v = w.1 then q else 0) =
      (X (⟨⟨v, hv⟩, j⟩ : SpatialVariable root) :
        MvPolynomial (SpatialVariable root)
          (MvPolynomial (SpatialVariable root) k)) * C q := by
  classical
  have hterm : ∀ w : OffRoot root,
      (if v = w.1 then q else 0) =
        if w = ⟨v, hv⟩ then q else 0 := by
    intro w
    by_cases h : v = w.1
    · have hw : w = ⟨v, hv⟩ := by
        apply Subtype.ext
        exact h.symm
      rw [if_pos h, if_pos hw]
    · have hw : w ≠ ⟨v, hv⟩ := by
        intro hw
        apply h
        simp [hw]
      rw [if_neg h, if_neg hw]
  have hprod : ∀ w : OffRoot root,
      (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if w = ⟨v, hv⟩ then q else 0) =
        if w = ⟨v, hv⟩ then
          X (⟨w, j⟩ : SpatialVariable root) * C q else 0 := by
    intro w
    by_cases hw : w = ⟨v, hv⟩
    · rw [if_pos hw, if_pos hw]
    · rw [if_neg hw, if_neg hw]
      simp
  simp_rw [hterm, hprod]
  rw [Fintype.sum_ite_eq']

/-- No member of the off-root subtype has underlying body equal to the
root. -/
theorem sum_X_C_if_root_eq
    {k V : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (j : Fin 3)
    (q : MvPolynomial (SpatialVariable root) k) :
    ∑ w : OffRoot root,
        (X (⟨w, j⟩ : SpatialVariable root) :
          MvPolynomial (SpatialVariable root)
            (MvPolynomial (SpatialVariable root) k)) *
          C (if root = w.1 then q else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w _hw
  have hrw : root ≠ w.1 := fun h ↦ w.2 h.symm
  simp [hrw]

/-- One spatial-coordinate slice of the grounded occurrence row. -/
theorem sum_occurrenceDirectionRow_mul_X
    {k V E : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) (j : Fin 3) :
    ∑ w : OffRoot root,
        C (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := k) root) e ⟨w, j⟩) * X ⟨w, j⟩ =
      (angularCoordinate (k := k) root (src e) j -
          angularCoordinate (k := k) root (dst e) j) *
        C (coefficientPlacement (k := k) root (src e) j -
          coefficientPlacement (k := k) root (dst e) j) := by
  classical
  simp only [occurrenceDirectionRow, map_add, add_mul,
    Finset.sum_add_distrib]
  by_cases hs : src e = root
  · have hd : dst e ≠ root := fun hd ↦ hLoop (hs.trans hd.symm)
    simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
      sum_X_C_if_root_eq, sum_X_C_if_eq_offRoot]
    ring
  · by_cases hd : dst e = root
    · simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
        sum_X_C_if_root_eq, sum_X_C_if_eq_offRoot]
    · simp [angularCoordinate, coefficientPlacement, hs, hd, mul_comm,
        sum_X_C_if_eq_offRoot]
      ring

/-- Summing one oriented row over grounded angular variables recovers the
corresponding angular/translational dot product. -/
theorem linearPolynomial_occurrenceDirectionRow
    {k V E : Type*} [CommRing k] [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) :
    coefficientLinearPolynomial
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := k) root) e) =
      Twist.splitKlein
        (iteratedGroundedTwist (k := k) root (src e) -
          iteratedGroundedTwist (k := k) root (dst e)) := by
  classical
  simp only [coefficientLinearPolynomial, Twist.splitKlein, Vec3.dot,
    Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [sum_occurrenceDirectionRow_mul_X root src dst e hLoop j]
  rw [iteratedGroundedTwist_fst_eq_angularCoordinate,
    iteratedGroundedTwist_fst_eq_angularCoordinate,
    iteratedGroundedTwist_snd, iteratedGroundedTwist_snd]
  rw [map_sub]

/-- A grounded Split--Klein occurrence equation becomes the literal linear
form of its grounded direction row. -/
theorem splitEquiv_symm_splitKlein_coefficientRelativeTwist
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (hLoop : src e ≠ dst e) :
    (splitEquiv (k := ℚ) root).symm
        (Twist.splitKlein
          (coefficientRelativeTwist root src dst e)) =
      coefficientLinearPolynomial
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := ℚ) root) e) := by
  apply (splitEquiv (k := ℚ) root).injective
  rw [(splitEquiv (k := ℚ) root).apply_symm_apply]
  rw [linearPolynomial_occurrenceDirectionRow root src dst e hLoop]
  change Twist.splitKlein (coefficientRelativeTwist root src dst e) =
    splitEquiv (k := ℚ) root
      (Twist.splitKlein
        (iteratedGroundedTwist (k := ℚ) root (src e) -
          iteratedGroundedTwist (k := ℚ) root (dst e)))
  let Z := iteratedGroundedTwist (k := ℚ) root (src e) -
    iteratedGroundedTwist (k := ℚ) root (dst e)
  calc
    Twist.splitKlein (coefficientRelativeTwist root src dst e) =
        Twist.splitKlein
          (mapTwist (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom Z) := by
      congr 1
      simp only [Z, coefficientRelativeTwist, mapTwist_sub]
      rw [map_iteratedGroundedTwist, map_iteratedGroundedTwist]
    _ = (splitEquiv (k := ℚ) root) (Twist.splitKlein Z) :=
      (WittShear.map_splitKlein
        (splitEquiv (k := ℚ) root).toRingEquiv.toRingHom Z).symm

end

end GroundedTwistSplit

end RB31E2E
