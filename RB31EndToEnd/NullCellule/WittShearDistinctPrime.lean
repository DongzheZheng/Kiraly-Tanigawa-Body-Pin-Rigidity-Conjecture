import RB31EndToEnd.NullCellule.SelectedDirectionHeight
import RB31EndToEnd.NullCellule.WittShear

/-!
# Witt shearing a surviving selected-null component to an injective placement

The complete distinctness denominator says that every labelled pair of
generic twists is nonzero.  One common rational Witt shear makes the
translational half of every such difference nonzero.  After the explicit
angular/translational split, the coefficient-prime quotient placement is
therefore injective.
-/

namespace RB31E2E

namespace WittShearDistinctPrime

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open UniversalHomogeneousChart
open SelectedNullHeight
open GroundedTwistSplit
open SelectedDirectionFibre
open PolynomialPrimeTrdegHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- The map from a prime polynomial ring to its quotient function field. -/
def primeFunctionFieldMap
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    R →+* FractionRing (R ⧸ P) :=
  (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp
    (Ideal.Quotient.mk P)

theorem primeFunctionFieldMap_eq_zero_iff
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (x : R) :
    primeFunctionFieldMap P x = 0 ↔ x ∈ P := by
  constructor
  · intro hx
    have hq : Ideal.Quotient.mk P x = 0 := by
      apply (FaithfulSMul.algebraMap_injective (R ⧸ P)
        (FractionRing (R ⧸ P)))
      change primeFunctionFieldMap P x = _
      simpa using hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro hx
    have hq : Ideal.Quotient.mk P x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simp [primeFunctionFieldMap, hq]

/-- Polynomial Witt shear of the root-zero universal twist assignment. -/
theorem map_coefficientGroundedTwist
    {V : Type*} [DecidableEq V] (root v : V) (s : Vec3 ℚ) :
    mapTwist (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (coefficientGroundedTwist root v) =
      WittShear.shear (fun j ↦ C (s j))
        (coefficientGroundedTwist root v) := by
  by_cases hv : v = root
  · subst v
    have hzero : coefficientGroundedTwist root root = 0 := by
      simp [coefficientGroundedTwist, extendOffRoot]
    rw [hzero, mapTwist_zero]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [WittShear.shear, Vec3.cross]
  · have hground : coefficientGroundedTwist root v =
        coefficientOffRootTwist ⟨v, hv⟩ := by
      simp [coefficientGroundedTwist, extendOffRoot, hv]
    rw [hground]
    change mapTwist
      (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (WittShear.universalTwist (k := ℚ) ⟨v, hv⟩) =
      WittShear.shear (fun j ↦ C (s j))
        (WittShear.universalTwist (k := ℚ) ⟨v, hv⟩)
    exact WittShear.map_universalTwist (U := OffRoot root) s ⟨v, hv⟩

theorem map_coefficientRelativeTwist
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (s : Vec3 ℚ) :
    mapTwist (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
        (coefficientRelativeTwist root src dst e) =
      WittShear.shear (fun j ↦ C (s j))
        (coefficientRelativeTwist root src dst e) := by
  rw [coefficientRelativeTwist, mapTwist_sub,
    map_coefficientGroundedTwist, map_coefficientGroundedTwist,
    ← WittShear.shear_sub]

/-- Every selected Split--Klein generator is fixed by the polynomial Witt
shear, including occurrences incident with the grounded root. -/
theorem algEquiv_coefficientNullEquation
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E) (s : Vec3 ℚ) :
    WittShear.algEquiv (U := OffRoot root) s
        (coefficientNullEquation root src dst e) =
      coefficientNullEquation root src dst e := by
  rw [coefficientNullEquation]
  change (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
      (Twist.splitKlein (coefficientRelativeTwist root src dst e)) = _
  rw [WittShear.map_splitKlein, map_coefficientRelativeTwist,
    WittShear.splitKlein_shear]

/-- The literal selected-null ideal is invariant under every rational Witt
shear. -/
theorem map_coefficientSelectedNullIdeal_algEquiv
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) (s : Vec3 ℚ) :
    Ideal.map
        (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv
        (coefficientSelectedNullIdeal root src dst active selected) =
      coefficientSelectedNullIdeal root src dst active selected := by
  rw [coefficientSelectedNullIdeal, Ideal.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨x, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, (algEquiv_coefficientNullEquation
      root src dst e.1.1 s).symm⟩
  · rintro ⟨e, rfl⟩
    refine ⟨coefficientNullEquation root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    exact algEquiv_coefficientNullEquation
      root src dst e.1.1 s

/-- Minimal primes transport through a ring equivalence. -/
theorem map_mem_minimalPrimes_of_equiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) :
    Ideal.map e P ∈ (Ideal.map e I).minimalPrimes := by
  let Q := Ideal.map e P
  have hQprime : Q.IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨⟨hQprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro J hJ hJQ
  letI : J.IsPrime := hJ.1
  have hJbackPrime : (Ideal.comap e J).IsPrime :=
    Ideal.IsPrime.comap e
  have hIback : I ≤ Ideal.comap e J :=
    Ideal.map_le_iff_le_comap.mp hJ.2
  have hbackP : Ideal.comap e J ≤ P := by
    intro x hx
    have hexJ : e x ∈ J := hx
    have hex : e x ∈ Q := hJQ hexJ
    obtain ⟨y, hyP, hyx⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).mp hex
    have : y = x := e.injective hyx
    simpa [this] using hyP
  have hPback : P ≤ Ideal.comap e J :=
    hP.2 ⟨hJbackPrime, hIback⟩ hbackP
  exact (Ideal.map_mono hPback).trans Ideal.map_comap_le

/-- A factor of the complete distinctness product cannot lie in a prime
which avoids that product. -/
theorem coefficientBodyDifferenceCoordinate_not_mem_of_denominator_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root))
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (uv : OrderedDistinctBodyPair V) :
    coefficientBodyDifferenceCoordinate root uv (chart uv) ∉ P := by
  intro hfactor
  apply hden
  rw [coefficientDistinctnessDenominator]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun w : OrderedDistinctBodyPair V ↦
      coefficientBodyDifferenceCoordinate root w (chart w))
    (Finset.mem_univ uv)]
  exact P.mul_mem_right _ hfactor

/-- Mapping a body-difference factor to the prime function field reads the
corresponding coordinate of the mapped relative twist. -/
theorem primeFunctionFieldMap_bodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    primeFunctionFieldMap P
        (coefficientBodyDifferenceCoordinate root uv c) =
      twistCoordinates
        (mapTwist (primeFunctionFieldMap P)
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2)) c := by
  rcases c with ⟨b, i⟩
  cases b <;>
    simp [coefficientBodyDifferenceCoordinate,
      coefficientGroundedCoordinate, twistCoordinates, mapTwist, mapVec3]

/-- Every pairwise twist difference is genuinely nonzero in the function
field of a component surviving the complete distinctness open. -/
theorem mapped_pairDifference_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (uv : OrderedDistinctBodyPair V) :
    mapTwist (primeFunctionFieldMap P)
      (coefficientGroundedTwist root uv.1.1 -
        coefficientGroundedTwist root uv.1.2) ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun Z ↦ twistCoordinates Z (chart uv)) hzero
  have hmapzero : primeFunctionFieldMap P
      (coefficientBodyDifferenceCoordinate root uv (chart uv)) = 0 := by
    rw [primeFunctionFieldMap_bodyDifferenceCoordinate]
    simpa using hcoord
  exact coefficientBodyDifferenceCoordinate_not_mem_of_denominator_not_mem
    root chart P hden uv
      ((primeFunctionFieldMap_eq_zero_iff P _).mp hmapzero)

/-- Ring maps commute with the explicit Witt shear when the shear parameter
is mapped coefficientwise. -/
theorem mapTwist_shear
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Vec3 R) (Z : Twist R) :
    mapTwist f (WittShear.shear s Z) =
      WittShear.shear (fun i ↦ f (s i)) (mapTwist f Z) := by
  apply Prod.ext
  · rfl
  · funext i
    change f (Z.2 i + Vec3.cross Z.1 s i) =
      f (Z.2 i) + Vec3.cross (fun j ↦ f (Z.1 j))
        (fun j ↦ f (s j)) i
    rw [map_add]
    congr 1
    fin_cases i <;> simp [Vec3.cross]

/-- A translational body-difference coordinate becomes the corresponding
coordinate of the sheared pairwise twist difference. -/
theorem algEquiv_translationalBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (i : Fin 3) (s : Vec3 ℚ) :
    WittShear.algEquiv (U := OffRoot root) s
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) =
      (WittShear.shear (fun j ↦ C (s j))
        (coefficientGroundedTwist root uv.1.1 -
          coefficientGroundedTwist root uv.1.2)).2 i := by
  have hmap := congrArg (fun Z ↦ Z.2 i)
    (show mapTwist
        (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv.toRingHom
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2) =
        WittShear.shear (fun j ↦ C (s j))
          (coefficientGroundedTwist root uv.1.1 -
            coefficientGroundedTwist root uv.1.2) by
      rw [mapTwist_sub, map_coefficientGroundedTwist,
        map_coefficientGroundedTwist, ← WittShear.shear_sub])
  simpa [coefficientBodyDifferenceCoordinate,
    coefficientGroundedCoordinate, mapTwist, mapVec3] using hmap

/-- Under the iterated split, a translational difference is a constant
coefficient polynomial in the outer angular variables. -/
theorem splitEquiv_symm_translationalBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (i : Fin 3) :
    (splitEquiv (k := ℚ) root).symm
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) =
      C (coefficientPlacement (k := ℚ) root uv.1.1 i -
        coefficientPlacement (k := ℚ) root uv.1.2 i) := by
  rw [map_sub]
  apply (splitEquiv (k := ℚ) root).injective
  rw [(splitEquiv (k := ℚ) root).apply_symm_apply, map_sub]
  change coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩ =
    splitEquiv (k := ℚ) root
        (C (coefficientPlacement root uv.1.1 i)) -
      splitEquiv (k := ℚ) root
        (C (coefficientPlacement root uv.1.2 i))
  have hu := congrArg (fun Z ↦ Z.2 i)
    (map_iteratedGroundedTwist root uv.1.1)
  have hv := congrArg (fun Z ↦ Z.2 i)
    (map_iteratedGroundedTwist root uv.1.2)
  change splitEquiv (k := ℚ) root
      ((iteratedGroundedTwist (k := ℚ) root uv.1.1).2 i) =
    (coefficientGroundedTwist root uv.1.1).2 i at hu
  change splitEquiv (k := ℚ) root
      ((iteratedGroundedTwist (k := ℚ) root uv.1.2).2 i) =
    (coefficientGroundedTwist root uv.1.2).2 i at hv
  rw [iteratedGroundedTwist_snd] at hu hv
  simpa [coefficientBodyDifferenceCoordinate,
    coefficientGroundedCoordinate] using
      (congrArg₂ (fun x y ↦ x - y) hu hv).symm

/-- A component surviving the complete distinctness open admits one
rational Witt shear whose split coefficient-prime placement is injective.
The transformed component is still a minimal selected-null component and
has the same height. -/
theorem exists_splitMinimalPrime_with_injective_placement
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (_hLoop : ∀ e ∈ active, src e ≠ dst e)
    (selected : Finset active) (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    ∃ (_s : Vec3 ℚ)
      (Psplit : Ideal (MvPolynomial (SpatialVariable root)
        (MvPolynomial (SpatialVariable root) ℚ)))
      (hp : (coefficientContraction Psplit).IsPrime),
      Psplit ∈ (splitSelectedNullIdeal
        root src dst active selected).minimalPrimes ∧
      Function.Injective
        (@quotientPlacement V _ root (coefficientContraction Psplit) hp) ∧
      Psplit.height = P.height := by
  classical
  let K := FractionRing (TwistCoefficientRing root ⧸ P)
  let φ : TwistCoefficientRing root →+* K := primeFunctionFieldMap P
  let Z : OrderedDistinctBodyPair V → Twist K := fun uv ↦
    mapTwist φ (coefficientGroundedTwist root uv.1.1 -
      coefficientGroundedTwist root uv.1.2)
  have hZ : ∀ uv, Z uv ≠ 0 := by
    intro uv
    exact mapped_pairDifference_ne_zero root chart P hden uv
  obtain ⟨s, hs⟩ := WittShear.exists_common_base_shear_snd_ne_zero
    (k := ℚ) Z hZ
  let e : TwistCoefficientRing root ≃+* TwistCoefficientRing root :=
    (WittShear.algEquiv (U := OffRoot root) s).toRingEquiv
  let Ps : Ideal (TwistCoefficientRing root) := Ideal.map e.symm P
  have hPsPrime : Ps.IsPrime := Ideal.map_isPrime_of_equiv e.symm
  letI : Ps.IsPrime := hPsPrime
  have hmapI : Ideal.map e.symm
      (coefficientSelectedNullIdeal root src dst active selected) =
      coefficientSelectedNullIdeal root src dst active selected := by
    have hinv := map_coefficientSelectedNullIdeal_algEquiv
      root src dst active selected (-s)
    have heq : e.symm =
        (WittShear.algEquiv (U := OffRoot root) (-s)).toRingEquiv := by
      ext x
      rfl
    rw [heq]
    exact hinv
  have hPs : Ps ∈ (coefficientSelectedNullIdeal
      root src dst active selected).minimalPrimes := by
    have hm := map_mem_minimalPrimes_of_equiv e.symm
      (coefficientSelectedNullIdeal root src dst active selected) P hP
    rw [hmapI] at hm
    exact hm
  let esplit := (splitEquiv (k := ℚ) root).symm.toRingEquiv
  let Psplit : Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ)) := Ideal.map esplit Ps
  have hPsplitPrime : Psplit.IsPrime := Ideal.map_isPrime_of_equiv esplit
  letI : Psplit.IsPrime := hPsplitPrime
  have hPsplit : Psplit ∈ (splitSelectedNullIdeal
      root src dst active selected).minimalPrimes := by
    exact map_mem_minimalPrimes_of_equiv esplit
      (coefficientSelectedNullIdeal root src dst active selected) Ps hPs
  have hplain : ∀ uv : OrderedDistinctBodyPair V,
      ∃ i : Fin 3,
        coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩ ∉ Ps := by
    intro uv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hs uv)
    refine ⟨i, ?_⟩
    intro hmem
    have hemem : e
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) ∈ P := by
      dsimp [Ps] at hmem
      rw [Ideal.map_symm] at hmem
      exact hmem
    have hzero : φ (e
        (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) = 0 :=
      (primeFunctionFieldMap_eq_zero_iff P _).2 hemem
    apply hi
    have hpoly := algEquiv_translationalBodyDifferenceCoordinate
      root uv i s
    have hcommute := mapTwist_shear φ (fun j ↦ C (s j))
      (coefficientGroundedTwist root uv.1.1 -
        coefficientGroundedTwist root uv.1.2)
    have hsparam : (fun j ↦ φ (C (s j))) =
        (fun j ↦ algebraMap ℚ K (s j)) := by
      funext j
      rfl
    have hcoord :
        φ (e (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) =
          (WittShear.shear (fun j ↦ algebraMap ℚ K (s j)) (Z uv)).2 i := by
      calc
        φ (e (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)) =
            φ ((WittShear.shear (fun j ↦ C (s j))
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2)).2 i) := by
          exact congrArg φ hpoly
        _ = (mapTwist φ
            (WittShear.shear (fun j ↦ C (s j))
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2))).2 i := rfl
        _ = (WittShear.shear (fun j ↦ φ (C (s j)))
            (mapTwist φ
              (coefficientGroundedTwist root uv.1.1 -
                coefficientGroundedTwist root uv.1.2))).2 i := by
          exact congrArg (fun T ↦ T.2 i) hcommute
        _ = (WittShear.shear
            (fun j ↦ algebraMap ℚ K (s j)) (Z uv)).2 i := by
          rw [hsparam]
    rw [hcoord] at hzero
    exact hzero
  have hinjective : Function.Injective
      (@quotientPlacement V _ root (coefficientContraction Psplit)
        (coefficientContraction_isPrime Psplit)) := by
    intro u v huv
    by_contra huvne
    let uv : OrderedDistinctBodyPair V := ⟨(u, v), huvne⟩
    obtain ⟨i, hi⟩ := hplain uv
    let p := coefficientContraction Psplit
    have hpPrime : p.IsPrime := coefficientContraction_isPrime Psplit
    letI : p.IsPrime := hpPrime
    have hcoordEq := congrFun huv i
    change quotientPlacement root p u i = quotientPlacement root p v i at hcoordEq
    have hzero : primeFunctionFieldMap p
        (coefficientPlacement root u i - coefficientPlacement root v i) = 0 := by
      change algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
          (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
        (Ideal.Quotient.mk p
          (coefficientPlacement root u i - coefficientPlacement root v i)) = 0
      rw [map_sub, map_sub, map_coefficientPlacement_eq_quotientPlacement,
        map_coefficientPlacement_eq_quotientPlacement, hcoordEq]
      exact sub_self _
    have hp : coefficientPlacement root u i -
        coefficientPlacement root v i ∈ p :=
      (primeFunctionFieldMap_eq_zero_iff p _).1 hzero
    have hC : C (coefficientPlacement root u i -
        coefficientPlacement root v i) ∈ Psplit := hp
    have hfactorSplit :=
      splitEquiv_symm_translationalBodyDifferenceCoordinate root uv i
    have hfactorPs : coefficientBodyDifferenceCoordinate
        root uv ⟨true, i⟩ ∈ Ps := by
      have himage : (splitEquiv (k := ℚ) root).symm
          (coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩) ∈
          Psplit := by
        rw [hfactorSplit]
        exact hC
      exact (Ideal.apply_mem_of_equiv_iff
        (I := Ps) (f := esplit)
        (x := coefficientBodyDifferenceCoordinate root uv ⟨true, i⟩)).1 himage
    exact hi hfactorPs
  let hp : (coefficientContraction Psplit).IsPrime :=
    coefficientContraction_isPrime Psplit
  refine ⟨s, Psplit, hp, hPsplit, ?_, ?_⟩
  · exact hinjective
  calc
    Psplit.height = Ps.height := esplit.height_map Ps
    _ = P.height := e.symm.height_map P

/-- Direct height of a surviving minimal selected-null component from the
grounded PF function-field theorem.  The terminal full-twist function-field
budget does not occur in the statement. -/
theorem coefficientMinimalPrime_height_ge_edgeCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (SpatialVariable root)) :
    (F.card : ℕ∞) ≤ P.height := by
  obtain ⟨_s, Psplit, hp, hPsplit, hinjective, hheight⟩ :=
    exists_splitMinimalPrime_with_injective_placement
      root src dst active hLoop
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented)
        chart P hP hden
  have hPsplitPrime : Psplit.IsPrime := hPsplit.1.1
  letI : Psplit.IsPrime := hPsplitPrime
  letI : (coefficientContraction Psplit).IsPrime := hp
  have hsplit :=
    SelectedDirectionHeight.splitMinimalPrime_height_ge_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented Psplit hPsplit hinjective hPF
  rw [← hheight]
  exact hsplit

end

end WittShearDistinctPrime

end RB31E2E
