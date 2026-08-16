import RB31EndToEnd.Incidence.TotalRingProvenanceSwap
import RB31EndToEnd.Incidence.ActivePinPrimeHeight

/-!
# Active-pin height in the pin-outer total ring

After `TotalRingProvenanceSwap`, the universal incidence algebra is written
as a polynomial ring in the labelled pin coordinates over the grounded-twist
coefficient ring.  This file performs the second, provenance-sensitive split:
for every active occurrence it puts the two chart-private pin coordinates in
the outer variable layer and puts the free pin coordinate (together with all
unused pin coordinates) in the coefficient layer.

The split is literal: the private-variable map is injective because its first
component is the occurrence label.  Thus different occurrences can never
silently reuse a private coordinate.  The selected angular coefficients are
then inverted in the twist coefficient ring.  In that chart the actual
compatibility pair is normalized to translated private coordinates.

No height, rank, or properness principle is assumed in this construction.
-/

namespace RB31E2E

namespace PinOuterActiveHeight

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart
open PinTriangularElimination
open TotalRingProvenanceSwap
open ActivePinPrimeHeight

/-! ## Twist coefficients before pin variables -/

/-- The grounded-twist coefficient ring in the pin-outer presentation. -/
abbrev TwistCoefficientRing {V : Type*} (root : V) :=
  MvPolynomial (GroundedTwistVariable root) ℚ

/-- One off-root universal twist in the coefficient ring. -/
def coefficientOffRootTwist {V : Type*} {root : V}
    (w : OffRoot root) : Twist (TwistCoefficientRing root) :=
  ⟨fun i ↦ X ⟨w, ⟨false, i⟩⟩,
    fun i ↦ X ⟨w, ⟨true, i⟩⟩⟩

/-- The root-zero universal twist assignment in the coefficient ring. -/
def coefficientGroundedTwist {V : Type*} [DecidableEq V] (root : V) :
    V → Twist (TwistCoefficientRing root) :=
  extendOffRoot root coefficientOffRootTwist

/-- Relative twist whose coordinates are still in the coefficient ring. -/
def coefficientRelativeTwist {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) : Twist (TwistCoefficientRing root) :=
  coefficientGroundedTwist root (src e) -
    coefficientGroundedTwist root (dst e)

@[simp]
theorem pinOuterOffRootTwist_eq_map_coefficientOffRootTwist
    {V E : Type*} {root : V} (w : OffRoot root) :
    pinOuterOffRootTwist (E := E) w =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientOffRootTwist w) := by
  apply Prod.ext <;> funext i <;> rfl

@[simp]
theorem pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
    {V E : Type*} [DecidableEq V] (root v : V) :
    pinOuterGroundedTwist (E := E) root v =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientGroundedTwist root v) := by
  by_cases hv : v = root
  · subst v
    simp [pinOuterGroundedTwist, coefficientGroundedTwist,
      extendOffRoot]
  · simp [pinOuterGroundedTwist, coefficientGroundedTwist,
      extendOffRoot, hv,
      pinOuterOffRootTwist_eq_map_coefficientOffRootTwist]

@[simp]
theorem pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
    {V E : Type*} [DecidableEq V] (root : V)
    (src dst : E → V) (e : E) :
    pinOuterRelativeTwist root src dst e =
      mapTwist (C : TwistCoefficientRing root →+*
        PinOuterRing root E) (coefficientRelativeTwist root src dst e) := by
  rw [pinOuterRelativeTwist, coefficientRelativeTwist, mapTwist_sub,
    pinOuterGroundedTwist_eq_map_coefficientGroundedTwist,
    pinOuterGroundedTwist_eq_map_coefficientGroundedTwist]

/-! ## Provenance-disjoint private variables -/

/-- The labelled pin variable occupied by a private chart slot of an active
occurrence. -/
def activePrivatePinVariable
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (q : active × Fin 2) : PinVariable E :=
  ⟨q.1.1, privateCoordinate (chart q.1) q.2⟩

/-- Occurrence provenance makes all selected private pin variables distinct. -/
theorem activePrivatePinVariable_injective
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) :
    Function.Injective (activePrivatePinVariable chart) := by
  rintro ⟨e, s⟩ ⟨f, t⟩ h
  have hef : e = f := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst f
  have hst : s = t :=
    privateCoordinate_injective (chart e) (congrArg Prod.snd h)
  subst t
  rfl

/-- The set of all selected private pin variables. -/
def activePrivatePinSet
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) : Set (PinVariable E) :=
  Set.range (activePrivatePinVariable chart)

/-- The subtype of labelled private pin variables. -/
abbrev ActivePrivatePin
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :=
  activePrivatePinSet active chart

/-- All pin variables not selected as private coordinates. -/
abbrev RetainedPin
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :=
  (activePrivatePinSet active chart)ᶜ

/-- An occurrence-slot pair as an element of the private-variable subtype. -/
def activePrivatePin
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (q : active × Fin 2) :
    ActivePrivatePin active chart :=
  ⟨activePrivatePinVariable chart q, ⟨q, rfl⟩⟩

/-- Every private-variable subtype element remembers a unique occurrence and
slot. -/
def activePrivatePinEquiv
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    active × Fin 2 ≃ ActivePrivatePin active chart :=
  {
    toFun := activePrivatePin chart
    invFun := fun p ↦ Classical.choose p.2
    left_inv := fun q ↦ by
      apply activePrivatePinVariable_injective chart
      exact Classical.choose_spec ((activePrivatePin chart q).2)
    right_inv := fun p ↦ by
      apply Subtype.ext
      exact Classical.choose_spec p.2
  }

@[simp]
theorem activePrivatePinEquiv_apply
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    (activePrivatePinEquiv active chart q : PinVariable E) =
      activePrivatePinVariable chart q := by
  rfl

/-- The free chart coordinate is never one of the private coordinates, even
when compared with every other occurrence. -/
theorem activeFreePinVariable_not_mem
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (e : active) :
    (⟨e.1, chart e⟩ : PinVariable E) ∉
      activePrivatePinSet active chart := by
  rintro ⟨⟨f, slot⟩, h⟩
  have hef : f = e := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst f
  exact privateCoordinate_ne (chart e) slot (congrArg Prod.snd h)

/-- The free pin coordinate as an element of the retained coefficient
variables. -/
def activeFreeRetainedPin
    {E : Type*} [DecidableEq E] {active : Finset E}
    (chart : active → Fin 3) (e : active) : RetainedPin active chart :=
  ⟨⟨e.1, chart e⟩, activeFreePinVariable_not_mem chart e⟩

/-! ## Splitting the pin polynomial layer -/

/-- Reindex all pin variables as private or retained, then make the private
variables the outer polynomial layer. -/
def splitPinVariables
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3) :
    MvPolynomial (PinVariable E) A ≃ₐ[A]
      MvPolynomial (ActivePrivatePin active chart)
        (MvPolynomial (RetainedPin active chart) A) :=
  by
    classical
    exact
      (renameEquiv A (Equiv.Set.sumCompl
          (activePrivatePinSet active chart)).symm).trans
        (sumAlgEquiv A (ActivePrivatePin active chart)
          (RetainedPin active chart))

@[simp]
theorem splitPinVariables_private_X
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3)
    (q : active × Fin 2) :
    splitPinVariables (A := A) active chart
        (X (activePrivatePinVariable chart q)) =
      X (activePrivatePin chart q) := by
  classical
  rw [splitPinVariables, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X,
    Equiv.Set.sumCompl_symm_apply_of_mem
      (show activePrivatePinVariable chart q ∈
        activePrivatePinSet active chart from ⟨q, rfl⟩),
    sumAlgEquiv_apply, sumToIter_Xl]
  rfl

@[simp]
theorem splitPinVariables_free_X
    {E A : Type*} [DecidableEq E] [CommSemiring A]
    (active : Finset E) (chart : active → Fin 3) (e : active) :
    splitPinVariables (A := A) active chart
        (X (⟨e.1, chart e⟩ : PinVariable E)) =
      C (X (activeFreeRetainedPin chart e)) := by
  classical
  rw [splitPinVariables, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X,
    Equiv.Set.sumCompl_symm_apply_of_notMem
      (activeFreePinVariable_not_mem chart e),
    sumAlgEquiv_apply, sumToIter_Xr]
  rfl

/-! ## The simultaneous angular localization -/

/-- The selected angular coefficient of one active relative twist. -/
def activeAngularCoefficient
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    TwistCoefficientRing root :=
  (coefficientRelativeTwist root src dst e.1).1 (chart e)

/-- Inverting one product simultaneously inverts every selected angular
coefficient. -/
def activeAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) : TwistCoefficientRing root :=
  ∏ e : active, activeAngularCoefficient root src dst active chart e

/-- The concrete coefficient localization used by the private-pin chart. -/
abbrev AngularCoefficientLocalization
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  Localization.Away
    (activeAngularDenominator root src dst active chart)

/-- Coefficients after retaining all non-private pin variables. -/
abbrev RetainedCoefficientRing
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  MvPolynomial (RetainedPin active chart)
    (AngularCoefficientLocalization root src dst active chart)

/-- Final private-variable presentation of the localized total ring. -/
abbrev PrivatePresentationRing
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :=
  MvPolynomial (ActivePrivatePin active chart)
    (RetainedCoefficientRing root src dst active chart)

theorem activeAngularCoefficient_dvd_denominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    activeAngularCoefficient root src dst active chart e ∣
      activeAngularDenominator root src dst active chart := by
  classical
  refine ⟨∏ f ∈ (Finset.univ.erase e),
    activeAngularCoefficient root src dst active chart f, ?_⟩
  simpa [activeAngularDenominator] using
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset active))
      (f := fun f ↦ activeAngularCoefficient
        root src dst active chart f)
      (Finset.mem_univ e)).symm

/-- A loopless occurrence has a genuinely nonzero labelled angular
coefficient. -/
theorem activeAngularCoefficient_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    activeAngularCoefficient root src dst active chart e ≠ 0 := by
  have hsd : src e.1 ≠ dst e.1 := hLoop e.1 e.2
  by_cases hs : src e.1 = root
  · have hd : dst e.1 ≠ root := by
      intro h
      exact hsd (hs.trans h.symm)
    simp [activeAngularCoefficient, coefficientRelativeTwist,
      coefficientGroundedTwist, extendOffRoot, hs, hd,
      coefficientOffRootTwist]
  · by_cases hd : dst e.1 = root
    · simp [activeAngularCoefficient, coefficientRelativeTwist,
        coefficientGroundedTwist, extendOffRoot, hs, hd,
        coefficientOffRootTwist]
    · intro hzero
      have hX :
          (X (⟨⟨src e.1, hs⟩, ⟨false, chart e⟩⟩ :
              GroundedTwistVariable root) : TwistCoefficientRing root) =
            (X (⟨⟨dst e.1, hd⟩, ⟨false, chart e⟩⟩ :
              GroundedTwistVariable root) : TwistCoefficientRing root) := by
        simpa [activeAngularCoefficient, coefficientRelativeTwist,
          coefficientGroundedTwist, extendOffRoot, hs, hd,
          coefficientOffRootTwist, sub_eq_zero] using hzero
      have hvar := MvPolynomial.X_injective hX
      exact hsd (congrArg (fun c : GroundedTwistVariable root ↦ c.1.1) hvar)

/-- The simultaneous angular denominator is nonzero for loopless active
occurrences. -/
theorem activeAngularDenominator_ne_zero
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    activeAngularDenominator root src dst active chart ≠ 0 := by
  classical
  rw [activeAngularDenominator]
  exact Finset.prod_ne_zero_iff.mpr fun e _ ↦
    activeAngularCoefficient_ne_zero
      root src dst active chart hLoop e

/-- The concrete away localization is a domain on every loopless chart. -/
@[reducible] def angularCoefficientLocalizationIsDomain
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (activeAngularDenominator_ne_zero
        root src dst active chart hLoop))

/-- Every selected angular coefficient is a unit in the simultaneous
localization. -/
theorem activeAngularCoefficient_isUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    IsUnit (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e)) := by
  apply isUnit_of_dvd_unit
    (map_dvd (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart))
      (activeAngularCoefficient_dvd_denominator
        root src dst active chart e))
  exact IsLocalization.Away.algebraMap_isUnit
    (S := AngularCoefficientLocalization root src dst active chart)
    (activeAngularDenominator root src dst active chart)

/-- The selected angular coefficient as an explicit unit. -/
def activeAngularUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    (AngularCoefficientLocalization root src dst active chart)ˣ :=
  (activeAngularCoefficient_isUnit root src dst active chart e).unit

@[simp]
theorem activeAngularUnit_coe
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    ((activeAngularUnit root src dst active chart e :
      (AngularCoefficientLocalization root src dst active chart)ˣ) :
      AngularCoefficientLocalization root src dst active chart) =
    algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e) := by
  exact (activeAngularCoefficient_isUnit
    root src dst active chart e).unit_spec

/-! ## The actual total-ring map into the private presentation -/

/-- Base-change the pin-outer polynomial ring to the angular localization
and then perform the private/retained variable split. -/
def localizedSplitPinOuterHom
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    PinOuterRing root E →+*
      PrivatePresentationRing root src dst active chart :=
  (splitPinVariables
      (A := AngularCoefficientLocalization root src dst active chart)
      active chart).toRingEquiv.toRingHom.comp
    (MvPolynomial.map (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)))

/-- The complete map from the original `Q[pin][twist]` presentation. -/
def localizedPrivatePresentationHom
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    RelativeRing root E →+*
      PrivatePresentationRing root src dst active chart :=
  (localizedSplitPinOuterHom root src dst active chart).comp
    (totalRingSwapHom (E := E) root)

@[simp]
theorem localizedSplitPinOuterHom_C
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (f : TwistCoefficientRing root) :
    localizedSplitPinOuterHom root src dst active chart (C f) =
      C (C (algebraMap (TwistCoefficientRing root)
        (AngularCoefficientLocalization root src dst active chart) f)) := by
  classical
  simp [localizedSplitPinOuterHom, splitPinVariables]

@[simp]
theorem localizedSplitPinOuterHom_private_X
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    localizedSplitPinOuterHom root src dst active chart
        (X (activePrivatePinVariable chart q)) =
      X (activePrivatePin chart q) := by
  classical
  simp [localizedSplitPinOuterHom]

@[simp]
theorem localizedSplitPinOuterHom_free_X
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedSplitPinOuterHom root src dst active chart
        (X (⟨e.1, chart e⟩ : PinVariable E)) =
      C (X (activeFreeRetainedPin chart e)) := by
  classical
  simp [localizedSplitPinOuterHom]

@[simp]
theorem localizedPrivatePresentationHom_privatePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (C (X (activePrivatePinVariable chart q))) =
      X (activePrivatePin chart q) := by
  simp [localizedPrivatePresentationHom]

@[simp]
theorem localizedPrivatePresentationHom_freePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedPrivatePresentationHom root src dst active chart
        (C (X (⟨e.1, chart e⟩ : PinVariable E))) =
      C (X (activeFreeRetainedPin chart e)) := by
  simp [localizedPrivatePresentationHom]

/-! ## Compatibility generators in retained/private normal form -/

/-- Mapping commutes with the explicit stationary-pin numerator. -/
theorem map_stationaryPinNumerator
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) (p : Vec3 R)
    (i j : Fin 3) :
    f (stationaryPinNumerator Z p i j) =
      stationaryPinNumerator (mapTwist f Z) (mapVec3 f p) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [stationaryPinNumerator, mapTwist, mapVec3]

/-- Mapping commutes with a triangular residual. -/
theorem map_triangularResidual
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) (p : Vec3 R)
    (i : Fin 3) (slot : Fin 2) :
    f (triangularResidual Z p i slot) =
      triangularResidual (mapTwist f Z) (mapVec3 f p) i slot := by
  simp [triangularResidual, map_stationaryPinNumerator, mapTwist, mapVec3]

theorem mapTwist_comp_local
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) (Z : Twist R) :
    mapTwist (g.comp f) Z = mapTwist g (mapTwist f Z) := by
  rfl

/-- The relative twist after localizing the twist coefficient ring. -/
def localizedCoefficientRelativeTwist
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) :
    Twist (AngularCoefficientLocalization root src dst active chart) :=
  mapTwist (algebraMap (TwistCoefficientRing root)
    (AngularCoefficientLocalization root src dst active chart))
    (coefficientRelativeTwist root src dst e)

/-- The same relative twist embedded in the retained-pin coefficient ring. -/
def retainedRelativeTwist
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) :
    Twist (RetainedCoefficientRing root src dst active chart) :=
  mapTwist (C : AngularCoefficientLocalization
      root src dst active chart →+*
      RetainedCoefficientRing root src dst active chart)
    (localizedCoefficientRelativeTwist
      root src dst active chart e)

/-- In the retained coefficient ring only the free chart coordinate of this
pin is needed by the stationary-pin numerator. -/
def retainedChartPin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    Vec3 (RetainedCoefficientRing root src dst active chart) :=
  fun j ↦ if j = chart e then X (activeFreeRetainedPin chart e) else 0

@[simp]
theorem retainedChartPin_free
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    retainedChartPin root src dst active chart e (chart e) =
      X (activeFreeRetainedPin chart e) := by
  simp [retainedChartPin]

theorem localizedPrivatePresentationHom_relativeTwist_angular
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) (i : Fin 3) :
    localizedPrivatePresentationHom root src dst active chart
        ((universalRelativeTwist root src dst e).1 i) =
      (C ((retainedRelativeTwist
        root src dst active chart e).1 i) :
        PrivatePresentationRing root src dst active chart) := by
  have hswap := congrArg (fun Z ↦ Z.1 i)
    (map_universalRelativeTwist (E := E) root src dst e)
  have hcoeff := congrArg (fun Z ↦ Z.1 i)
    (pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
      root src dst e)
  change totalRingSwapHom (E := E) root
      ((universalRelativeTwist root src dst e).1 i) =
    (pinOuterRelativeTwist root src dst e).1 i at hswap
  change (pinOuterRelativeTwist root src dst e).1 i =
    C ((coefficientRelativeTwist root src dst e).1 i) at hcoeff
  rw [localizedPrivatePresentationHom]
  change localizedSplitPinOuterHom root src dst active chart
      (totalRingSwapHom (E := E) root
        ((universalRelativeTwist root src dst e).1 i)) = _
  rw [hswap, hcoeff, localizedSplitPinOuterHom_C]
  rfl

theorem localizedPrivatePresentationHom_relativeTwist_translational
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : E) (i : Fin 3) :
    localizedPrivatePresentationHom root src dst active chart
        ((universalRelativeTwist root src dst e).2 i) =
      (C ((retainedRelativeTwist
        root src dst active chart e).2 i) :
        PrivatePresentationRing root src dst active chart) := by
  have hswap := congrArg (fun Z ↦ Z.2 i)
    (map_universalRelativeTwist (E := E) root src dst e)
  have hcoeff := congrArg (fun Z ↦ Z.2 i)
    (pinOuterRelativeTwist_eq_map_coefficientRelativeTwist
      root src dst e)
  change totalRingSwapHom (E := E) root
      ((universalRelativeTwist root src dst e).2 i) =
    (pinOuterRelativeTwist root src dst e).2 i at hswap
  change (pinOuterRelativeTwist root src dst e).2 i =
    C ((coefficientRelativeTwist root src dst e).2 i) at hcoeff
  rw [localizedPrivatePresentationHom]
  change localizedSplitPinOuterHom root src dst active chart
      (totalRingSwapHom (E := E) root
        ((universalRelativeTwist root src dst e).2 i)) = _
  rw [hswap, hcoeff, localizedSplitPinOuterHom_C]
  rfl

@[simp]
theorem localizedPrivatePresentationHom_pin_private
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (universalParameterPin (root := root) e.1
          (privateCoordinate (chart e) slot)) =
      (X (activePrivatePin chart ⟨e, slot⟩) :
        PrivatePresentationRing root src dst active chart) := by
  exact localizedPrivatePresentationHom_privatePin
    root src dst active chart ⟨e, slot⟩

@[simp]
theorem localizedPrivatePresentationHom_pin_free
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    localizedPrivatePresentationHom root src dst active chart
        (universalParameterPin (root := root) e.1 (chart e)) =
      (C (retainedChartPin root src dst active chart e (chart e)) :
        PrivatePresentationRing root src dst active chart) := by
  rw [retainedChartPin_free]
  exact localizedPrivatePresentationHom_freePin
    root src dst active chart e

/-- The scalar numerator occurring on one private slot.  Writing the six
branches directly keeps the total-ring proof small: only the free pin
coordinate occurs. -/
def retainedPrivateNumerator
    {R : Type*} [CommRing R] (Z : Twist R) (free : R)
    (i : Fin 3) (slot : Fin 2) : R :=
  if i = 0 then
    if slot = 0 then Z.1 1 * free - Z.2 2
    else Z.2 1 + Z.1 2 * free
  else if i = 1 then
    if slot = 0 then Z.2 2 + Z.1 0 * free
    else Z.1 2 * free - Z.2 0
  else
    if slot = 0 then Z.1 0 * free - Z.2 1
    else Z.2 0 + Z.1 1 * free

theorem retainedPrivateNumerator_eq_stationaryPinNumerator
    {R : Type*} [CommRing R] (Z : Twist R) (p : Vec3 R)
    (i : Fin 3) (slot : Fin 2) :
    retainedPrivateNumerator Z (p i) i slot =
      stationaryPinNumerator Z p i (privateCoordinate i slot) := by
  fin_cases i <;> fin_cases slot <;>
    simp [retainedPrivateNumerator, stationaryPinNumerator,
      privateCoordinate]

/-- At a private coordinate, the mapped stationary numerator contains no
private pin variable: it lies literally in the retained coefficient ring. -/
theorem localizedPrivatePresentationHom_stationaryPinNumerator_private
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (stationaryPinNumerator
          (universalRelativeTwist root src dst e.1)
          (universalParameterPin (root := root) e.1)
          (chart e) (privateCoordinate (chart e) slot)) =
      C (stationaryPinNumerator
        (retainedRelativeTwist root src dst active chart e.1)
        (retainedChartPin root src dst active chart e)
        (chart e) (privateCoordinate (chart e) slot)) := by
  let hDomain : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (AngularCoefficientLocalization
      root src dst active chart) := hDomain.toNontrivial
  generalize hi : chart e = i
  have hfree :
      localizedPrivatePresentationHom root src dst active chart
          (universalParameterPin (root := root) e.1 i) =
        (C (X (activeFreeRetainedPin chart e)) :
          PrivatePresentationRing root src dst active chart) := by
    have h := localizedPrivatePresentationHom_pin_free
      root src dst active chart e
    rw [retainedChartPin_free] at h
    simpa [hi] using h
  have hang (j : Fin 3) :=
    localizedPrivatePresentationHom_relativeTwist_angular
      root src dst active chart e.1 j
  have htrans (j : Fin 3) :=
    localizedPrivatePresentationHom_relativeTwist_translational
      root src dst active chart e.1 j
  let f := localizedPrivatePresentationHom root src dst active chart
  have hmulSub (a p b : RelativeRing root E)
      (A P B : RetainedCoefficientRing root src dst active chart)
      (ha : f a = C A) (hp : f p = C P) (hb : f b = C B) :
      f (a * p - b) = C (A * P - B) := by
    have hneg : f (-b) = C (-B) := by
      apply add_right_cancel (b := C B)
      calc
        f (-b) + C B = f (-b) + f b := by rw [hb]
        _ = f (-b + b) := (f.map_add _ _).symm
        _ = f 0 := congrArg f (neg_add_cancel b)
        _ = 0 := f.map_zero
        _ = C (-B) + C B := by
          calc
            0 = C 0 := (C.map_zero).symm
            _ = C (-B + B) := congrArg C (neg_add_cancel B).symm
            _ = C (-B) + C B := C.map_add _ _
    rw [sub_eq_add_neg, f.map_add, f.map_mul, hneg,
      ha, hp]
    simp [sub_eq_add_neg]
  have haddMul (b a p : RelativeRing root E)
      (B A P : RetainedCoefficientRing root src dst active chart)
      (hb : f b = C B) (ha : f a = C A) (hp : f p = C P) :
      f (b + a * p) = C (B + A * P) := by
    rw [f.map_add, f.map_mul, hb, ha, hp]
    simp
  have hretfree :
      retainedChartPin root src dst active chart e i =
        X (activeFreeRetainedPin chart e) := by
    simpa [hi] using retainedChartPin_free
      root src dst active chart e
  rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
  rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
  rw [hretfree]
  fin_cases i <;> fin_cases slot
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 1)
        (universalParameterPin (root := root) e.1 0)
        ((universalRelativeTwist root src dst e.1).2 2)
        ((retainedRelativeTwist root src dst active chart e.1).1 1)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 2)
        (hang 1) hfree (htrans 2)
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 1)
        ((universalRelativeTwist root src dst e.1).1 2)
        (universalParameterPin (root := root) e.1 0)
        ((retainedRelativeTwist root src dst active chart e.1).2 1)
        ((retainedRelativeTwist root src dst active chart e.1).1 2)
        (X (activeFreeRetainedPin chart e))
        (htrans 1) (hang 2) hfree
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 2)
        ((universalRelativeTwist root src dst e.1).1 0)
        (universalParameterPin (root := root) e.1 1)
        ((retainedRelativeTwist root src dst active chart e.1).2 2)
        ((retainedRelativeTwist root src dst active chart e.1).1 0)
        (X (activeFreeRetainedPin chart e))
        (htrans 2) (hang 0) hfree
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 2)
        (universalParameterPin (root := root) e.1 1)
        ((universalRelativeTwist root src dst e.1).2 0)
        ((retainedRelativeTwist root src dst active chart e.1).1 2)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 0)
        (hang 2) hfree (htrans 0)
  · simpa [retainedPrivateNumerator, hi] using
      hmulSub
        ((universalRelativeTwist root src dst e.1).1 0)
        (universalParameterPin (root := root) e.1 2)
        ((universalRelativeTwist root src dst e.1).2 1)
        ((retainedRelativeTwist root src dst active chart e.1).1 0)
        (X (activeFreeRetainedPin chart e))
        ((retainedRelativeTwist root src dst active chart e.1).2 1)
        (hang 0) hfree (htrans 1)
  · simpa [retainedPrivateNumerator, hi] using
      haddMul
        ((universalRelativeTwist root src dst e.1).2 0)
        ((universalRelativeTwist root src dst e.1).1 1)
        (universalParameterPin (root := root) e.1 2)
        ((retainedRelativeTwist root src dst active chart e.1).2 0)
        ((retainedRelativeTwist root src dst active chart e.1).1 1)
        (X (activeFreeRetainedPin chart e))
        (htrans 0) (hang 1) hfree

/-! ## Unit normalization of the actual triangular residual -/

/-- The selected angular coefficient, now as a unit of the retained-pin
coefficient ring. -/
def retainedAngularUnit
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    (RetainedCoefficientRing root src dst active chart)ˣ :=
  Units.map
    (C : AngularCoefficientLocalization root src dst active chart →+*
      RetainedCoefficientRing root src dst active chart)
    (activeAngularUnit root src dst active chart e)

@[simp]
theorem retainedAngularUnit_coe
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) :
    ((retainedAngularUnit root src dst active chart e :
      (RetainedCoefficientRing root src dst active chart)ˣ) :
      RetainedCoefficientRing root src dst active chart) =
      (retainedRelativeTwist root src dst active chart e.1).1
        (chart e) := by
  change C (((activeAngularUnit root src dst active chart e :
      (AngularCoefficientLocalization root src dst active chart)ˣ) :
      AngularCoefficientLocalization root src dst active chart)) =
    C (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization root src dst active chart)
      (activeAngularCoefficient root src dst active chart e))
  rw [activeAngularUnit_coe]

/-- The retained coefficient on the right of one normalized private
relation. -/
def privateRelationRhs
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    RetainedCoefficientRing root src dst active chart :=
  (((retainedAngularUnit root src dst active chart e)⁻¹ :
      (RetainedCoefficientRing root src dst active chart)ˣ) :
      RetainedCoefficientRing root src dst active chart) *
    retainedPrivateNumerator
      (retainedRelativeTwist root src dst active chart e.1)
      (X (activeFreeRetainedPin chart e)) (chart e) slot

/-- Literal translated-coordinate normal form associated with one active
occurrence and one private slot. -/
def normalizedPrivateGenerator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (e : active) (slot : Fin 2) :
    PrivatePresentationRing root src dst active chart :=
  (X (activePrivatePin chart ⟨e, slot⟩) :
      PrivatePresentationRing root src dst active chart) +
    (C (-privateRelationRhs root src dst active chart e slot) :
      PrivatePresentationRing root src dst active chart)

/-- Before division by the angular unit, the actual universal triangular
residual has the expected private-linear form. -/
theorem localizedPrivatePresentationHom_universalTriangularResidual
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    localizedPrivatePresentationHom root src dst active chart
        (universalTriangularResidual root src dst e.1 (chart e) slot) =
      (C ((retainedRelativeTwist root src dst active chart e.1).1
            (chart e)) : PrivatePresentationRing
              root src dst active chart) *
          (X (activePrivatePin chart ⟨e, slot⟩) :
            PrivatePresentationRing root src dst active chart) +
        (C (-retainedPrivateNumerator
            (retainedRelativeTwist root src dst active chart e.1)
            (X (activeFreeRetainedPin chart e)) (chart e) slot) :
          PrivatePresentationRing root src dst active chart) := by
  let hDomain : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (AngularCoefficientLocalization
      root src dst active chart) := hDomain.toNontrivial
  let f := localizedPrivatePresentationHom root src dst active chart
  let Z := universalRelativeTwist root src dst e.1
  let p := universalParameterPin (root := root) e.1
  let numerator := stationaryPinNumerator Z p (chart e)
    (privateCoordinate (chart e) slot)
  have hangular : f (Z.1 (chart e)) =
      C ((retainedRelativeTwist
        root src dst active chart e.1).1 (chart e)) :=
    localizedPrivatePresentationHom_relativeTwist_angular
      root src dst active chart e.1 (chart e)
  have hprivate : f (p (privateCoordinate (chart e) slot)) =
      X (activePrivatePin chart ⟨e, slot⟩) :=
    localizedPrivatePresentationHom_pin_private
      root src dst active chart e slot
  have hnumerator : f numerator = C
      (retainedPrivateNumerator
        (retainedRelativeTwist root src dst active chart e.1)
        (X (activeFreeRetainedPin chart e)) (chart e) slot) := by
    dsimp [numerator, Z, p]
    rw [localizedPrivatePresentationHom_stationaryPinNumerator_private
      root src dst active chart hLoop e slot]
    rw [← retainedPrivateNumerator_eq_stationaryPinNumerator]
    rw [retainedChartPin_free]
  let N := retainedPrivateNumerator
    (retainedRelativeTwist root src dst active chart e.1)
    (X (activeFreeRetainedPin chart e)) (chart e) slot
  have hneg : f (-numerator) = C (-N) := by
    apply add_right_cancel (b := C N)
    calc
      f (-numerator) + C N = f (-numerator) + f numerator := by
        rw [hnumerator]
      _ = f (-numerator + numerator) := (f.map_add _ _).symm
      _ = f 0 := congrArg f (neg_add_cancel numerator)
      _ = 0 := f.map_zero
      _ = C (-N) + C N := by
        calc
          0 = C 0 := (C.map_zero).symm
          _ = C (-N + N) := congrArg C (neg_add_cancel N).symm
          _ = C (-N) + C N := C.map_add _ _
  change f (triangularResidual Z p (chart e) slot) = _
  rw [triangularResidual, sub_eq_add_neg,
    f.map_add, f.map_mul, hneg, hangular, hprivate]

/-- Dividing by the selected angular unit turns the actual residual into the
literal translated private coordinate `X_private - rhs`. -/
theorem normalize_localized_universalTriangularResidual
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (e : active) (slot : Fin 2) :
    C ((((retainedAngularUnit root src dst active chart e)⁻¹ :
        (RetainedCoefficientRing root src dst active chart)ˣ) :
        RetainedCoefficientRing root src dst active chart)) *
      localizedPrivatePresentationHom root src dst active chart
        (universalTriangularResidual root src dst e.1 (chart e) slot) =
      normalizedPrivateGenerator root src dst active chart e slot := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  rw [localizedPrivatePresentationHom_universalTriangularResidual
    root src dst active chart hLoop e slot]
  rw [normalizedPrivateGenerator, privateRelationRhs,
    ← retainedAngularUnit_coe]
  let u := retainedAngularUnit root src dst active chart e
  let N := retainedPrivateNumerator
    (retainedRelativeTwist root src dst active chart e.1)
    (X (activeFreeRetainedPin chart e)) (chart e) slot
  change C ((↑(u⁻¹) : RetainedCoefficientRing
      root src dst active chart)) *
      (C ((↑u : RetainedCoefficientRing
        root src dst active chart)) *
          X (activePrivatePin chart ⟨e, slot⟩) + C (-N)) =
      X (activePrivatePin chart ⟨e, slot⟩) +
        C (-((↑(u⁻¹) : RetainedCoefficientRing
          root src dst active chart) * N))
  rw [mul_add, ← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul,
    ← C_mul]
  congr 2
  exact mul_neg
    ((↑(u⁻¹) : RetainedCoefficientRing root src dst active chart)) N

/-! ## Simultaneous height of all active private pairs -/

/-- The retained-coordinate response attached to a labelled private pin
variable.  The inverse equivalence recovers the unique occurrence and slot,
so the right-hand side cannot lose its provenance. -/
def activePrivateTranslation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (p : ActivePrivatePin active chart) :
    RetainedCoefficientRing root src dst active chart :=
  let q := (activePrivatePinEquiv active chart).symm p
  privateRelationRhs root src dst active chart q.1 q.2

@[simp]
theorem activePrivateTranslation_activePrivatePin
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) (q : active × Fin 2) :
    activePrivateTranslation root src dst active chart
        (activePrivatePin chart q) =
      privateRelationRhs root src dst active chart q.1 q.2 := by
  change privateRelationRhs root src dst active chart
      ((activePrivatePinEquiv active chart).symm
        ((activePrivatePinEquiv active chart) q)).1
      ((activePrivatePinEquiv active chart).symm
        ((activePrivatePinEquiv active chart) q)).2 = _
  rw [Equiv.symm_apply_apply]

/-- Enumerate the two private variables of every active occurrence by
`Fin (active.card * 2)`. -/
def activePrivateEnumeration
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Fin (active.card * 2) → ActivePrivatePin active chart :=
  occurrencePrivateVariable
    (fun i slot ↦
      activePrivatePin chart ⟨active.equivFin.symm i, slot⟩)

/-- The enumeration remains injective: the finite enumeration of active
occurrences and the labelled private-pin equivalence are both injective. -/
theorem activePrivateEnumeration_injective
    {E : Type*} [DecidableEq E] (active : Finset E)
    (chart : active → Fin 3) :
    Function.Injective (activePrivateEnumeration active chart) := by
  apply occurrencePrivateVariable_injective
  intro q r hqr
  have hpairs :
      (active.equivFin.symm q.1, q.2) =
        (active.equivFin.symm r.1, r.2) :=
    (activePrivatePinEquiv active chart).injective hqr
  apply Prod.ext
  · exact active.equivFin.symm.injective (congrArg Prod.fst hpairs)
  · exact congrArg (fun p : active × Fin 2 ↦ p.2) hpairs

/-- The literal ideal generated by every normalized active compatibility
relation, indexed by its occurrence and private slot. -/
def activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    Ideal (PrivatePresentationRing root src dst active chart) :=
  Ideal.span (Set.range (fun q : active × Fin 2 ↦
    normalizedPrivateGenerator
      root src dst active chart q.1 q.2))

/-- Every enumerated translated coordinate is one of the literal normalized
relations.  This is the ideal-level provenance bridge needed by the height
chain; it assumes no abstract presentation map. -/
theorem translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    translatedCoordinateIdeal
        (activePrivateEnumeration active chart)
        (activePrivateTranslation root src dst active chart) ≤
      activeNormalizedPrivateIdeal root src dst active chart := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  rw [translatedCoordinateIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  let q : Fin active.card × Fin 2 := finProdFinEquiv.symm j
  let e : active := active.equivFin.symm q.1
  have hmem : normalizedPrivateGenerator
      root src dst active chart e q.2 ∈
      activeNormalizedPrivateIdeal root src dst active chart := by
    apply Ideal.subset_span
    exact ⟨⟨e, q.2⟩, rfl⟩
  have henum : activePrivateEnumeration active chart j =
      activePrivatePin chart ⟨e, q.2⟩ := by
    rfl
  have hCneg (a : RetainedCoefficientRing
      root src dst active chart) :
      (C (-a) : PrivatePresentationRing
        root src dst active chart) = -C a :=
    map_neg C a
  change X (activePrivateEnumeration active chart j) -
      C (activePrivateTranslation root src dst active chart
        (activePrivateEnumeration active chart j)) ∈
    activeNormalizedPrivateIdeal root src dst active chart
  rw [henum, activePrivateTranslation_activePrivatePin,
    sub_eq_add_neg, ← hCneg]
  simpa only [normalizedPrivateGenerator] using hmem

/-- Main simultaneous increment theorem: after the concrete angular
localization, the actual normalized active relations contribute at least two
height units for every active occurrence. -/
theorem activeNormalizedPrivateIdeal_height_ge_twice_card
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    (active.card * 2 : ℕ) ≤
      (activeNormalizedPrivateIdeal
        root src dst active chart).height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  exact (translatedCoordinateIdeal_height_ge_card
      (activePrivateEnumeration active chart)
      (activePrivateEnumeration_injective active chart)
      (activePrivateTranslation root src dst active chart)).trans
    (Ideal.height_mono
      (translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
        root src dst active chart hLoop))

/-! ## Returning from normal form to the actual compatibility equations -/

/-- The localized ideal generated by the two oriented compatibility
coordinates of every active occurrence.  Each oriented generator is
definitionally a genuine universal compatibility coordinate or its negative;
the sign has no effect on the generated ideal. -/
def localizedActiveCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3) :
    Ideal (PrivatePresentationRing root src dst active chart) :=
  Ideal.span (Set.range (fun q : active × Fin 2 ↦
    localizedPrivatePresentationHom root src dst active chart
      (universalOrientedCompatibilityEquation
        root src dst q.1.1 (chart q.1) q.2)))

/-- Unit normalization identifies the ideal of the actual oriented
compatibility pairs with the literal translated-private-coordinate ideal. -/
theorem localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    localizedActiveCompatibilityIdeal root src dst active chart =
      activeNormalizedPrivateIdeal root src dst active chart := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  apply le_antisymm
  · rw [localizedActiveCompatibilityIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    have hn : normalizedPrivateGenerator
        root src dst active chart q.1 q.2 ∈
        activeNormalizedPrivateIdeal root src dst active chart := by
      apply Ideal.subset_span
      exact ⟨q, rfl⟩
    have hu := Ideal.mul_mem_left
      (activeNormalizedPrivateIdeal root src dst active chart)
      (C (((retainedAngularUnit
        root src dst active chart q.1 :
          (RetainedCoefficientRing
            root src dst active chart)ˣ) :
          RetainedCoefficientRing root src dst active chart))) hn
    have hnormalize :=
      normalize_localized_universalTriangularResidual
        root src dst active chart hLoop q.1 q.2
    rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at hnormalize
    rw [← hnormalize, ← mul_assoc, ← C_mul,
      Units.mul_inv, C_1, one_mul] at hu
    exact hu
  · rw [activeNormalizedPrivateIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    have hr : localizedPrivatePresentationHom
        root src dst active chart
        (universalOrientedCompatibilityEquation
          root src dst q.1.1 (chart q.1) q.2) ∈
        localizedActiveCompatibilityIdeal
          root src dst active chart := by
      apply Ideal.subset_span
      exact ⟨q, rfl⟩
    have hu := Ideal.mul_mem_left
      (localizedActiveCompatibilityIdeal root src dst active chart)
      (C (((retainedAngularUnit
        root src dst active chart q.1)⁻¹ :
          (RetainedCoefficientRing
            root src dst active chart)ˣ) :
          RetainedCoefficientRing root src dst active chart)) hr
    have hnormalize :=
      normalize_localized_universalTriangularResidual
        root src dst active chart hLoop q.1 q.2
    rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at hnormalize
    rw [hnormalize] at hu
    exact hu

/-- Final active-compatibility height theorem in the concrete pin-outer
presentation: the original two compatibility equations per loopless active
occurrence have height at least `2 * active.card` after inverting exactly the
selected angular factors. -/
theorem localizedActiveCompatibilityIdeal_height_ge_twice_card
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (chart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active chart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active chart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active chart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active chart) := inferInstance
    (active.card * 2 : ℕ) ≤
      (localizedActiveCompatibilityIdeal
        root src dst active chart).height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active chart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active chart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active chart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active chart) := inferInstance
  rw [localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
    root src dst active chart hLoop]
  exact activeNormalizedPrivateIdeal_height_ge_twice_card
    root src dst active chart hLoop

end

end PinOuterActiveHeight

end RB31E2E
