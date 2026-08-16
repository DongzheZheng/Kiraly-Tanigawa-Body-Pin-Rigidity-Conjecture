import RB31EndToEnd.Incidence.PinOuterActiveHeight
import RB31EndToEnd.Incidence.UniversalFullProvenanceChartContraction
import RB31EndToEnd.Incidence.UniversalActivePinHeightTransfer
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Full-provenance transfer for the pin-outer active-height theorem

This file connects the concrete private-pin height calculation to the exact
finite-generic prime-height interface.  The route is explicit:

* contract a finite-generic prime through the pin-coefficient localization;
* swap the pin and twist polynomial layers;
* localize the selected angular product and split private from retained pins;
* use the actual compatibility equations to add two height units per active
  occurrence; and
* localize the retained coefficient prime at the complete pairwise-distinct
  factor.

Consequently the only remaining height input is the height of the selected
null ideal in the retained coefficient ring where both the angular and the
pairwise-distinct provenance factors are invertible.  No presentation map or
coordinate-change hypothesis is an input to the final theorem.
-/

namespace RB31E2E

namespace PinOuterFullProvenanceHeightTransfer

noncomputable section

open MvPolynomial
open GroundedTwistPolynomial
open UniversalHomogeneousChart
open PinTriangularElimination
open TotalRingProvenanceSwap
open PinOuterActiveHeight
open ActivePinPrimeHeight
open UniversalActivePinHeightTransfer

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The complete provenance denominator in twist coefficients -/

/-- One grounded twist coordinate before adjoining any pin variables. -/
def coefficientGroundedCoordinate
    {V : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) : TwistCoefficientRing root :=
  if c.1 then
    (coefficientGroundedTwist root v).2 c.2
  else
    (coefficientGroundedTwist root v).1 c.2

/-- A labelled body-difference coordinate in the twist coefficient ring. -/
def coefficientBodyDifferenceCoordinate
    {V : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    TwistCoefficientRing root :=
  coefficientGroundedCoordinate root uv.1.1 c -
    coefficientGroundedCoordinate root uv.1.2 c

/-- The complete pairwise-distinct factor before adjoining pin variables. -/
def coefficientDistinctnessDenominator
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    TwistCoefficientRing root :=
  ∏ uv : OrderedDistinctBodyPair V,
    coefficientBodyDifferenceCoordinate root uv (chart uv)

/-- The complete pairwise-distinct times active-angular coefficient product. -/
def coefficientIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) : TwistCoefficientRing root :=
  coefficientDistinctnessDenominator root distinctChart *
    activeAngularDenominator root src dst active angularChart

theorem totalRingSwapHom_universalGroundedCoordinate
    {V E : Type*} [DecidableEq V] (root v : V)
    (c : TwistCoordinate) :
    totalRingSwapHom (E := E) root
        (universalGroundedCoordinate (E := E) root v c) =
      C (coefficientGroundedCoordinate root v c) := by
  rcases c with ⟨b, i⟩
  cases b
  · have hswap := congrArg (fun Z ↦ Z.1 i)
      (map_universalGroundedTwist (E := E) root v)
    have hcoefficient := congrArg (fun Z ↦ Z.1 i)
      (pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
        (E := E) root v)
    exact hswap.trans hcoefficient
  · have hswap := congrArg (fun Z ↦ Z.2 i)
      (map_universalGroundedTwist (E := E) root v)
    have hcoefficient := congrArg (fun Z ↦ Z.2 i)
      (pinOuterGroundedTwist_eq_map_coefficientGroundedTwist
        (E := E) root v)
    exact hswap.trans hcoefficient

theorem totalRingSwapHom_universalBodyDifferenceCoordinate
    {V E : Type*} [DecidableEq V] (root : V)
    (uv : OrderedDistinctBodyPair V) (c : TwistCoordinate) :
    totalRingSwapHom (E := E) root
        (universalBodyDifferenceCoordinate (E := E) root uv c) =
      C (coefficientBodyDifferenceCoordinate root uv c) := by
  rw [universalBodyDifferenceCoordinate,
    coefficientBodyDifferenceCoordinate, map_sub,
    totalRingSwapHom_universalGroundedCoordinate,
    totalRingSwapHom_universalGroundedCoordinate, map_sub]

theorem totalRingSwapHom_universalDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (chart : DistinctnessChart V) :
    totalRingSwapHom (E := E) root
        (universalDistinctnessDenominator (E := E) root chart) =
      C (coefficientDistinctnessDenominator root chart) := by
  rw [universalDistinctnessDenominator,
    coefficientDistinctnessDenominator, map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro uv _huv
  exact totalRingSwapHom_universalBodyDifferenceCoordinate
    (E := E) root uv (chart uv)

theorem coefficientBodyDifferenceCoordinate_active_eq
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    coefficientBodyDifferenceCoordinate root
        ⟨(src e.1, dst e.1), hLoop e.1 e.2⟩
        ⟨false, angularChart e⟩ =
      activeAngularCoefficient
        root src dst active angularChart e := by
  rfl

theorem totalRingSwapHom_universalActiveAngularFactor
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (e : active) :
    totalRingSwapHom (E := E) root
        (universalActiveAngularFactor
          root src dst active hLoop angularChart e) =
      C (activeAngularCoefficient
        root src dst active angularChart e) := by
  rw [universalActiveAngularFactor,
    totalRingSwapHom_universalBodyDifferenceCoordinate]
  exact congrArg C
    (coefficientBodyDifferenceCoordinate_active_eq
      root src dst active hLoop angularChart e)

theorem totalRingSwapHom_universalAngularDenominator
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) :
    totalRingSwapHom (E := E) root
        (universalAngularDenominator
          root src dst active hLoop angularChart) =
      C (activeAngularDenominator
        root src dst active angularChart) := by
  rw [universalAngularDenominator, activeAngularDenominator,
    map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro e _he
  exact totalRingSwapHom_universalActiveAngularFactor
    root src dst active hLoop angularChart e

/-- The full denominator really is coefficient-valued after the total-ring
swap; no pin variable is hidden in the localization factor. -/
theorem totalRingSwapHom_universalIncidenceProvenanceDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3) :
    totalRingSwapHom (E := E) root
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart) =
      C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart) := by
  rw [universalIncidenceProvenanceDenominator,
    coefficientIncidenceProvenanceDenominator, map_mul,
    totalRingSwapHom_universalDistinctnessDenominator,
    totalRingSwapHom_universalAngularDenominator, map_mul]

/-! ## The selected-null ideal in retained coefficients -/

theorem map_splitKlein_local
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Z : Twist R) :
    f (Twist.splitKlein Z) =
      Twist.splitKlein (mapTwist f Z) := by
  simp [Twist.splitKlein, Vec3.dot, mapTwist, mapVec3]

/-- A selected null equation after angular localization and absorption of
all non-private pin variables into the coefficient ring. -/
def retainedNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    RetainedCoefficientRing root src dst active angularChart :=
  Twist.splitKlein
    (retainedRelativeTwist root src dst active angularChart e)

theorem localizedPrivatePresentationHom_universalNullEquation
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (e : E) :
    localizedPrivatePresentationHom
        root src dst active angularChart
        (universalNullEquation root src dst e) =
      (C (retainedNullEquation
        root src dst active angularChart e) :
        PrivatePresentationRing root src dst active angularChart) := by
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let f := localizedPrivatePresentationHom
    root src dst active angularChart
  have htwist : mapTwist f
      (universalRelativeTwist root src dst e) =
      mapTwist (C : RetainedCoefficientRing
          root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart)
        (retainedRelativeTwist
          root src dst active angularChart e) := by
    apply Prod.ext <;> funext i
    · exact localizedPrivatePresentationHom_relativeTwist_angular
        root src dst active angularChart e i
    · exact localizedPrivatePresentationHom_relativeTwist_translational
        root src dst active angularChart e i
  rw [universalNullEquation, map_splitKlein_local, htwist]
  exact (map_splitKlein_local
    (C : RetainedCoefficientRing
        root src dst active angularChart →+*
        PrivatePresentationRing root src dst active angularChart)
    (retainedRelativeTwist
      root src dst active angularChart e)).symm

/-- The selected-null ideal before the private polynomial variables are
adjoined. -/
def retainedSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal (RetainedCoefficientRing
      root src dst active angularChart) :=
  Ideal.span (Set.range (fun e : SelectedOccurrence active selected ↦
    retainedNullEquation
      root src dst active angularChart e.1.1))

/-- Mapping the literal universal selected-null ideal lands exactly in the
constant extension of the retained selected-null ideal. -/
theorem map_selectedNullIdeal_eq_map_C_retainedSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal.map
        (localizedPrivatePresentationHom
          root src dst active angularChart)
        (Ideal.span
          (selectedNullGeneratorSet
            root src dst active selected)) =
      Ideal.map
        (C : RetainedCoefficientRing
            root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart)
        (retainedSelectedNullIdeal
          root src dst active angularChart selected) := by
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  rw [Ideal.map_span, retainedSelectedNullIdeal, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    exact ⟨retainedNullEquation
        root src dst active angularChart e.1.1,
        ⟨⟨e, rfl⟩,
        (localizedPrivatePresentationHom_universalNullEquation
          root src dst active angularChart e.1.1).symm⟩⟩
  · rintro ⟨g, ⟨e, rfl⟩, rfl⟩
    exact ⟨selectedNullGenerator root src dst active selected e,
        ⟨⟨e, rfl⟩,
        localizedPrivatePresentationHom_universalNullEquation
          root src dst active angularChart e.1.1⟩⟩

/-! ## Pairwise-distinct localization after the angular chart -/

/-- The pairwise-distinct factor inside the retained coefficient ring. -/
def retainedDistinctnessDenominator
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V) :
    RetainedCoefficientRing root src dst active angularChart :=
  C (algebraMap (TwistCoefficientRing root)
      (AngularCoefficientLocalization
        root src dst active angularChart)
      (coefficientDistinctnessDenominator root distinctChart))

/-- Retained coefficients on the chart where both angular and complete
pairwise-distinct provenance factors are invertible. -/
abbrev IncidenceLocalizedRetainedCoefficientRing
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V) :=
  Localization.Away
    (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart)

/-- The sole remaining ideal after both provenance localizations. -/
def incidenceLocalizedSelectedNullIdeal
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) :
    Ideal (IncidenceLocalizedRetainedCoefficientRing
      root src dst active angularChart distinctChart) :=
  Ideal.map
    (algebraMap
      (RetainedCoefficientRing root src dst active angularChart)
      (IncidenceLocalizedRetainedCoefficientRing
        root src dst active angularChart distinctChart))
    (retainedSelectedNullIdeal
      root src dst active angularChart selected)

/-- The Krull height of the preceding ideal, packaged with one coherent
choice of commutative-ring instances for the iterated polynomial
localizations. -/
def incidenceLocalizedSelectedNullIdealHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V) : ℕ∞ :=
  let R := RetainedCoefficientRing
    root src dst active angularChart
  letI : CommRing R := inferInstance
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  letI : CommRing T := inferInstance
  let I : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  let J : Ideal T := Ideal.map (algebraMap R T) I
  J.height

/-! ## Height-preserving changes of presentation -/

/-- Contracting through generic pin coefficients and undoing the finite
twist reindexing preserves ideal height.  This is the precise bridge from
the finite-generic presentation back to the original total ring. -/
theorem finiteGenericChartHom_height_comap
    {V E : Type*} [Fintype V] [DecidableEq V]
    (root : V) (Q : Ideal (FiniteGenericRelativeRing root E)) :
    (Ideal.comap (finiteGenericChartHom root) Q).height = Q.height := by
  let e := MvPolynomial.renameEquiv (GenericPinCoefficientField E)
    (finiteTwistIndexEquiv root)
  let Qg : Ideal (GenericRelativeRing root E) :=
    Ideal.comap e.toRingEquiv.toRingHom Q
  change (Ideal.comap (genericCoefficientExtensionHom root) Qg).height =
    Q.height
  calc
    (Ideal.comap (genericCoefficientExtensionHom root) Qg).height =
        Qg.height := by
      change (Ideal.comap
        (algebraMap (RelativeRing root E)
          (GenericRelativeRing root E)) Qg).height = Qg.height
      exact IsLocalization.height_comap
        ((nonZeroDivisors (PinParameterRing E)).map
          (C : PinParameterRing E →+* RelativeRing root E)) Qg
    _ = Q.height := by
      exact RingEquiv.height_comap e.toRingEquiv Q

/-- Avoiding the selected angular product is exactly the disjointness needed
to localize the pin-outer ring coefficientwise. -/
theorem localizedSplitPinOuterHom_height_map
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular :
      C (activeAngularDenominator
        root src dst active angularChart) ∉ P) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active angularChart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active angularChart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active angularChart) := inferInstance
    (Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P).height = P.height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  letI : CommRing A := inferInstance
  letI : CommRing (MvPolynomial (PinVariable E) A) := inferInstance
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  have hlocalization : Pangular.height = P.height := by
    change (Ideal.map
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A)) P).height = P.height
    exact IsLocalization.height_map_of_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E)) P hdisj
  rw [localizedSplitPinOuterHom, ← Ideal.map_map]
  change (Ideal.map
    (splitPinVariables (A := A) active angularChart).toRingEquiv.toRingHom
    Pangular).height = P.height
  exact (RingEquiv.height_map
    (splitPinVariables (A := A) active angularChart).toRingEquiv
    Pangular).trans hlocalization

/-- The angular-localized private-presentation image of a disjoint prime is
again prime. -/
theorem localizedSplitPinOuterHom_isPrime
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular :
      C (activeAngularDenominator
        root src dst active angularChart) ∉ P) :
    (Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P).IsPrime := by
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  letI : Pangular.IsPrime := by
    change (Ideal.map
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A)) P).IsPrime
    exact IsLocalization.isPrime_of_isPrime_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E))
      (MvPolynomial (PinVariable E) A) P inferInstance hdisj
  rw [localizedSplitPinOuterHom, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv
    (splitPinVariables (A := A) active angularChart).toRingEquiv

/-- Avoidance of the complete coefficient product implies avoidance of its
angular factor. -/
theorem angularDenominator_not_mem_of_incidenceDenominator_not_mem
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E))
    (hfull : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P) :
    C (activeAngularDenominator
      root src dst active angularChart) ∉ P := by
  intro hAngular
  apply hfull
  rw [coefficientIncidenceProvenanceDenominator, map_mul]
  exact P.mul_mem_left _ hAngular

/-- Avoidance of the complete coefficient product also implies avoidance of
its pairwise-distinct factor. -/
theorem distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (distinctChart : DistinctnessChart V)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E))
    (hfull : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P) :
    C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P := by
  intro hDistinct
  apply hfull
  rw [coefficientIncidenceProvenanceDenominator, map_mul]
  exact P.mul_mem_right _ hDistinct

/-! ## Literal source-ideal bridges -/

/-- Each sign-oriented compatibility equation is one of the two literal
active compatibility generators, up to multiplication by `-1`. -/
theorem universalOrientedCompatibilityEquation_mem_activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (q : active × Fin 2) :
    universalOrientedCompatibilityEquation
        root src dst q.1.1 (angularChart q.1) q.2 ∈
      activeCompatibilityIdeal
        root src dst active angularChart := by
  have hne_general (i : Fin 3) (slot : Fin 2) :
      solvingCompatibilityCoordinate i slot ≠ i := by
    fin_cases i <;> fin_cases slot <;> decide
  have hne : solvingCompatibilityCoordinate
      (angularChart q.1) q.2 ≠ angularChart q.1 :=
    hne_general (angularChart q.1) q.2
  let a : ActiveCompatibilityIndex active angularChart :=
    ⟨q.1, ⟨solvingCompatibilityCoordinate
      (angularChart q.1) q.2, hne⟩⟩
  have hgenerator : universalCompatibilityCoordinate
      root src dst q.1.1
        (solvingCompatibilityCoordinate (angularChart q.1) q.2) ∈
      activeCompatibilityIdeal
        root src dst active angularChart := by
    change activeCompatibilityGenerator
      root src dst active angularChart a ∈
        activeCompatibilityIdeal root src dst active angularChart
    exact Ideal.subset_span ⟨a, rfl⟩
  rcases universalTriangularResidual_eq_compatibility_or_neg
      root src dst q.1.1 (angularChart q.1) q.2 with h | h
  · rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at h
    rw [h]
    exact hgenerator
  · rw [universalTriangularResidual_eq_orientedCompatibilityEquation]
      at h
    rw [h]
    exact (activeCompatibilityIdeal
      root src dst active angularChart).neg_mem hgenerator

theorem activeCompatibilityIdeal_le_universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    activeCompatibilityIdeal root src dst active angularChart ≤
      universalChartIdeal
        root src dst active angularChart selected := by
  rw [activeCompatibilityIdeal, universalChartIdeal,
    universalChartGeneratorSet, Ideal.span_union]
  exact le_sup_left

theorem selectedNullIdeal_le_universalChartIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active) :
    Ideal.span (selectedNullGeneratorSet
        root src dst active selected) ≤
      universalChartIdeal
        root src dst active angularChart selected := by
  rw [universalChartIdeal, universalChartGeneratorSet,
    Ideal.span_union]
  exact le_sup_right

/-- The concrete localized active ideal is generated by images of literal
source-chart generators. -/
theorem localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) :
    localizedActiveCompatibilityIdeal
        root src dst active angularChart ≤
      Ideal.map
        (localizedPrivatePresentationHom
          root src dst active angularChart)
        (activeCompatibilityIdeal
          root src dst active angularChart) := by
  rw [localizedActiveCompatibilityIdeal, Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  exact Ideal.mem_map_of_mem _
    (universalOrientedCompatibilityEquation_mem_activeCompatibilityIdeal
      root src dst active angularChart q)

/-- A polynomial avoided by a prime before angular localization remains
avoided after the coefficient localization and variable-splitting
equivalence. -/
theorem localizedSplitPinOuterHom_not_mem_map_of_not_mem
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (P : Ideal (PinOuterRing root E)) [P.IsPrime]
    (hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P)
    (x : PinOuterRing root E) (hx : x ∉ P) :
    localizedSplitPinOuterHom
        root src dst active angularChart x ∉
      Ideal.map
        (localizedSplitPinOuterHom
          root src dst active angularChart) P := by
  let A := AngularCoefficientLocalization
    root src dst active angularChart
  let f : PinOuterRing root E →+* MvPolynomial (PinVariable E) A :=
    MvPolynomial.map
      (algebraMap (TwistCoefficientRing root) A)
  let e := (splitPinVariables
    (A := A) active angularChart).toRingEquiv
  let Pangular : Ideal (MvPolynomial (PinVariable E) A) :=
    Ideal.map f P
  have hdisj : Disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E) : Set (PinOuterRing root E))
      (P : Set (PinOuterRing root E)) := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem
      (C (activeAngularDenominator
        root src dst active angularChart))
      (Ideal.IsPrime.isRadical inferInstance)).2 hAngular
  have hcomap : Ideal.comap f Pangular = P := by
    change Ideal.comap
      (algebraMap (PinOuterRing root E)
        (MvPolynomial (PinVariable E) A))
      (Ideal.map
        (algebraMap (PinOuterRing root E)
          (MvPolynomial (PinVariable E) A)) P) = P
    exact IsLocalization.comap_map_of_isPrime_disjoint
      ((Submonoid.powers
        (activeAngularDenominator
          root src dst active angularChart)).map
        (C : TwistCoefficientRing root →+*
          PinOuterRing root E))
      (MvPolynomial (PinVariable E) A) inferInstance hdisj
  intro hxmap
  have hefx : e (f x) ∈ Ideal.map e Pangular := by
    change e (f x) ∈ Ideal.map (e.toRingHom.comp f) P at hxmap
    rw [← Ideal.map_map] at hxmap
    exact hxmap
  have hfx : f x ∈ Pangular := by
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := Pangular) (f := e) (y := e (f x))).2 hefx
    simpa using hback
  apply hx
  rw [← hcomap]
  exact hfx

/-! ## Unconditional relative height of the actual compatibility summand -/

/-- In the concrete angular pin-outer presentation, every prime containing
the actual active compatibility ideal has at least two height units per
active occurrence above its retained-coefficient contraction. -/
theorem privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (Q : Ideal (PrivatePresentationRing
      root src dst active angularChart)) [Q.IsPrime]
    (hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ Q) :
    letI : IsDomain (AngularCoefficientLocalization
        root src dst active angularChart) :=
      angularCoefficientLocalizationIsDomain
        root src dst active angularChart hLoop
    letI : Nontrivial (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : IsDomain (RetainedCoefficientRing
        root src dst active angularChart) := inferInstance
    letI : CommRing (PrivatePresentationRing
        root src dst active angularChart) := inferInstance
    (Ideal.comap
        (C : RetainedCoefficientRing
            root src dst active angularChart →+*
          PrivatePresentationRing
            root src dst active angularChart) Q).height +
        (2 * active.card : ℕ) ≤ Q.height := by
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let S := PrivatePresentationRing
    root src dst active angularChart
  let P : Ideal R := Ideal.comap (C : R →+* S) Q
  letI : P.IsPrime := by
    dsimp [P]
    exact Ideal.comap_isPrime _ _
  let c : Fin (active.card * 2) → ActivePrivatePin active angularChart :=
    activePrivateEnumeration active angularChart
  let a : ActivePrivatePin active angularChart → R :=
    activePrivateTranslation root src dst active angularChart
  let I₀ : Ideal S :=
    basePrimeCoordinateIdeal P (Set.range c)
  let τ : S ≃+* S :=
    (coordinateTranslationEquiv (fun x ↦ -a x)).toRingEquiv
  let Iₜ : Ideal S := Ideal.map τ I₀
  have hconstant : Ideal.map τ
      (Ideal.map (C : R →+* S) P) =
      Ideal.map (C : R →+* S) P := by
    rw [show Ideal.map τ
          (Ideal.map (C : R →+* S) P) =
        Ideal.map (τ.toRingHom.comp C) P by
          exact Ideal.map_map C τ.toRingHom]
    congr 1
    apply DFunLike.ext _ _
    intro r
    exact coordinateTranslationEquiv_C (fun x ↦ -a x) r
  have htranslated : Iₜ =
      Ideal.map (C : R →+* S) P ⊔
        translatedCoordinateIdeal c a := by
    dsimp [Iₜ, I₀]
    rw [basePrimeCoordinateIdeal, Ideal.map_sup,
      hconstant]
    congr 1
    exact (translatedCoordinateIdeal_eq_map_coordinateVariableIdeal
      c a).symm
  have hnormalized : activeNormalizedPrivateIdeal
      root src dst active angularChart ≤ Q := by
    rw [← localizedActiveCompatibilityIdeal_eq_activeNormalizedPrivateIdeal
      root src dst active angularChart hLoop]
    exact hcompat
  have htranslated_le : translatedCoordinateIdeal c a ≤ Q := by
    exact (translatedCoordinateIdeal_le_activeNormalizedPrivateIdeal
      root src dst active angularChart hLoop).trans hnormalized
  have hIₜ : Iₜ ≤ Q := by
    rw [htranslated]
    apply sup_le
    · exact Ideal.map_comap_le
    · exact htranslated_le
  have hI₀ : P.height + (active.card * 2 : ℕ) ≤ I₀.height := by
    exact basePrimeCoordinateIdeal_height_ge_add_card
      P c (activePrivateEnumeration_injective active angularChart)
  calc
    P.height + (2 * active.card : ℕ) =
        P.height + (active.card * 2 : ℕ) := by
      rw [Nat.mul_comm]
    _ ≤ I₀.height := hI₀
    _ = Iₜ.height := (RingEquiv.height_map τ I₀).symm
    _ ≤ Q.height := Ideal.height_mono hIₜ

/-! ## Reduction to the selected-null height statement -/

/-- The complete finite-generic provenance height condition follows from
one presentation-invariant statement: the selected null ideal has its
expected height after localizing the retained coefficient ring at both the
active-angular and complete pairwise-distinct factors.

The preceding comparison theorems account for all changes of presentation
and for the `2 * active.card` contribution of the compatibility equations. -/
theorem finiteGenericIncidenceProvenancePrimeHeightCondition_of_incidenceLocalizedSelectedNullIdeal_height
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hcard : selected.card =
      6 * (Fintype.card V - 1) - 2 * active.card)
    (hselected : (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart) :
    FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart selected distinctChart := by
  intro Q hQprime _hQhom hchart hdenominator
  letI : Q.IsPrime := hQprime
  let P₀ : Ideal (RelativeRing root E) :=
    Ideal.comap (finiteGenericChartHom root) Q
  letI : P₀.IsPrime := by
    dsimp [P₀]
    exact Ideal.comap_isPrime _ _
  let swap : RelativeRing root E ≃+* PinOuterRing root E :=
    (totalRingSwap (E := E) root).toRingEquiv
  let P₁ : Ideal (PinOuterRing root E) := Ideal.map swap P₀
  letI : P₁.IsPrime := by
    dsimp [P₁]
    exact Ideal.map_isPrime_of_equiv swap
  have hfullP₀ : universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ P₀ := by
    simpa [P₀, finiteGenericIncidenceProvenanceDenominator] using
      hdenominator
  have hfullP₁ : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P₁ := by
    intro hx
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := P₀) (f := swap)
      (y := C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart))).2 hx
    have hswap :=
      totalRingSwapHom_universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart
    have hinverse : swap.symm
        (C (coefficientIncidenceProvenanceDenominator
          root src dst active distinctChart angularChart)) =
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart := by
      rw [← hswap]
      change swap.symm (swap
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart)) = _
      exact swap.symm_apply_apply _
    apply hfullP₀
    simpa [hinverse] using hback
  have hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P₁ :=
    angularDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  have hDistinctSource : C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P₁ :=
    distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  let P₂ : Ideal (PrivatePresentationRing
      root src dst active angularChart) :=
    Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P₁
  letI : P₂.IsPrime := by
    dsimp [P₂]
    exact localizedSplitPinOuterHom_isPrime
      root src dst active angularChart P₁ hAngular
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let Cₚ : R →+* PrivatePresentationRing
      root src dst active angularChart := C
  let Pcoeff : Ideal R := Ideal.comap Cₚ P₂
  letI : Pcoeff.IsPrime := by
    dsimp [Pcoeff]
    exact Ideal.comap_isPrime _ _
  have hsource : universalChartIdeal
      root src dst active angularChart selected ≤ P₀ := by
    intro f hf
    change finiteGenericChartHom root f ∈ Q
    exact hchart (Ideal.mem_map_of_mem _ hf)
  have hactiveSource : activeCompatibilityIdeal
      root src dst active angularChart ≤ P₀ :=
    (activeCompatibilityIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have hselectedSource : Ideal.span
      (selectedNullGeneratorSet root src dst active selected) ≤ P₀ :=
    (selectedNullIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have himage : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart) P₀ = P₂ := by
    dsimp [P₂, P₁]
    rw [localizedPrivatePresentationHom, ← Ideal.map_map]
    rfl
  have hmappedActive : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart)
      (activeCompatibilityIdeal
        root src dst active angularChart) ≤ P₂ := by
    rw [← himage]
    exact Ideal.map_mono hactiveSource
  have hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ P₂ :=
    (localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
      root src dst active angularChart).trans hmappedActive
  let Iselected : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  have hretainedSelected : Iselected ≤ Pcoeff := by
    dsimp [Iselected]
    rw [Ideal.span_le]
    rintro _ ⟨e, rfl⟩
    change C (retainedNullEquation
      root src dst active angularChart e.1.1) ∈ P₂
    rw [← localizedPrivatePresentationHom_universalNullEquation
      root src dst active angularChart e.1.1, ← himage]
    exact Ideal.mem_map_of_mem _
      (hselectedSource (Ideal.subset_span ⟨e, rfl⟩))
  have hrelative : Pcoeff.height + (2 * active.card : ℕ) ≤
      P₂.height := by
    simpa [Pcoeff, Cₚ, R] using
      (privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
        root src dst active angularChart hLoop P₂ hcompat)
  have hP₀height : P₀.height = Q.height := by
    exact finiteGenericChartHom_height_comap root Q
  have hP₁height : P₁.height = P₀.height := by
    exact RingEquiv.height_map swap P₀
  have hP₂height : P₂.height = P₁.height := by
    exact localizedSplitPinOuterHom_height_map
      root src dst active angularChart hLoop P₁ hAngular
  have hP₂heightQ : P₂.height = Q.height :=
    hP₂height.trans (hP₁height.trans hP₀height)
  have hDistinctAfterAngular :=
    localizedSplitPinOuterHom_not_mem_map_of_not_mem
      root src dst active angularChart P₁ hAngular
        (C (coefficientDistinctnessDenominator root distinctChart))
        hDistinctSource
  have hretainedDistinct : retainedDistinctnessDenominator
      root src dst active angularChart distinctChart ∉ Pcoeff := by
    intro hx
    apply hDistinctAfterAngular
    change C (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart) ∈ P₂ at hx
    simpa [P₂, retainedDistinctnessDenominator] using hx
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  let Pfull : Ideal T := Ideal.map
    (algebraMap R T) Pcoeff
  have hdisjDistinct : Disjoint
      (Submonoid.powers d : Set R)
      (Pcoeff : Set R) :=
    (Ideal.disjoint_powers_iff_notMem
      d
      (Ideal.IsPrime.isRadical inferInstance)).2 hretainedDistinct
  have hPfullHeight : Pfull.height = Pcoeff.height := by
    dsimp [Pfull, T]
    exact IsLocalization.height_map_of_disjoint
      (Submonoid.powers d)
      Pcoeff hdisjDistinct
  let Ifull : Ideal T := Ideal.map (algebraMap R T) Iselected
  have hselectedFull : Ifull ≤ Pfull := by
    dsimp [Ifull, Pfull]
    exact Ideal.map_mono hretainedSelected
  have hselectedHeight : (selected.card : ℕ∞) ≤ Ifull.height := by
    simpa [incidenceLocalizedSelectedNullIdealHeight, R, d, T,
      Iselected, Ifull] using hselected
  have hselectedCoeff : (selected.card : ℕ∞) ≤ Pcoeff.height := by
    calc
      (selected.card : ℕ∞) ≤ Ifull.height := hselectedHeight
      _ ≤ Pfull.height := Ideal.height_mono hselectedFull
      _ = Pcoeff.height := hPfullHeight
  have hbudget := universalChartGenerator_budget
    root active angularChart selected hcard
  rw [card_activeCompatibilityIndex] at hbudget
  have hbudgetTop : (groundedTwistVariableCount root : ℕ∞) ≤
      ((2 * active.card + selected.card : ℕ) : ℕ∞) := by
    exact_mod_cast hbudget
  calc
    (groundedTwistVariableCount root : ℕ∞) ≤
        ((2 * active.card + selected.card : ℕ) : ℕ∞) := hbudgetTop
    _ = (selected.card : ℕ∞) + (2 * active.card : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (add_comm (2 * (active.card : ℕ∞))
          (selected.card : ℕ∞))
    _ ≤ Pcoeff.height + (2 * active.card : ℕ) := by
      simpa [add_comm] using
        (add_le_add_right hselectedCoeff
          (2 * active.card : ℕ∞))
    _ ≤ P₂.height := hrelative
    _ = Q.height := hP₂heightQ

end

end PinOuterFullProvenanceHeightTransfer

end RB31E2E
