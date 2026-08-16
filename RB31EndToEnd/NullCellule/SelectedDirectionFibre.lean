import RB31EndToEnd.Algebra.CoefficientLinearFibre
import RB31EndToEnd.Algebra.FractionQuotientCoordinates
import RB31EndToEnd.Incidence.SkeletonOccurrenceSelection
import RB31EndToEnd.NullCellule.GroundedTwistSplit
import RB31EndToEnd.NullCellule.SelectedNullHeight

/-!
# Selected Split--Klein fibres are grounded direction systems

After the explicit angular/translational split, the selected null ideal is
a coefficient-linear row ideal.  At every coefficient prime its generic
fibre is therefore the literal grounded direction-row ideal, with the
original selected occurrence provenance retained.
-/

namespace RB31E2E

namespace SelectedDirectionFibre

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open UniversalHomogeneousChart
open PolynomialPrimeTrdegHeight
open GroundedTwistSplit
open CoefficientLinearFibre

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The selected null ideal transported to the iterated
`Q[translation][angular]` presentation. -/
def splitSelectedNullIdeal
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (selected : Finset active) :
    Ideal (MvPolynomial (SpatialVariable root)
      (MvPolynomial (SpatialVariable root) ℚ)) :=
  Ideal.map (splitEquiv (k := ℚ) root).symm.toRingEquiv
    (SelectedNullHeight.coefficientSelectedNullIdeal
      root src dst active selected)

/-- The split selected-null ideal is literally the coefficient-linear ideal
of its oriented grounded occurrence rows. -/
theorem splitSelectedNullIdeal_eq_linearFormIdealOver
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (selected : Finset active) :
    splitSelectedNullIdeal root src dst active selected =
      linearFormIdealOver
        (fun e : SelectedOccurrence active selected ↦
          occurrenceDirectionRow root src dst
            (coefficientPlacement (k := ℚ) root) e.1.1) := by
  classical
  rw [splitSelectedNullIdeal,
    SelectedNullHeight.coefficientSelectedNullIdeal, Ideal.map_span,
    linearFormIdealOver]
  congr 1
  ext g
  constructor
  · rintro ⟨q, ⟨e, rfl⟩, rfl⟩
    refine ⟨e, ?_⟩
    symm
    change (splitEquiv (k := ℚ) root).symm
      (Twist.splitKlein
        (coefficientRelativeTwist root src dst e.1.1)) = _
    exact splitEquiv_symm_splitKlein_coefficientRelativeTwist
      root src dst e.1.1 (hLoop e.1.1 e.1.2)
  · rintro ⟨e, rfl⟩
    refine ⟨SelectedNullHeight.coefficientNullEquation
      root src dst e.1.1, ⟨e, rfl⟩, ?_⟩
    change (splitEquiv (k := ℚ) root).symm
      (Twist.splitKlein
        (coefficientRelativeTwist root src dst e.1.1)) = _
    exact splitEquiv_symm_splitKlein_coefficientRelativeTwist
      root src dst e.1.1 (hLoop e.1.1 e.1.2)

/-- The coefficient-prime quotient function field placement, grounded at
`root`. -/
def quotientPlacement
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    V → Fin 3 →
      FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p) :=
  fun v i ↦ if h : v = root then 0 else
    FractionQuotientCoordinates.coordinate p ⟨⟨v, h⟩, i⟩

@[simp] theorem quotientPlacement_root
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    quotientPlacement root p root = 0 := by
  funext i
  simp [quotientPlacement]

/-- The quotient placement coordinates generate the coefficient function
field; the grounded zero coordinates introduce no extra generator. -/
theorem quotientPlacement_generated
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime] :
    IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦
        quotientPlacement root p x.1 x.2)) = ⊤ := by
  let K := FractionRing
    (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
  let L : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ
      (Set.range (fun x : V × Fin 3 ↦
        quotientPlacement root p x.1 x.2))
  apply top_unique
  have hcoord := FractionQuotientCoordinates.adjoin_coordinate_eq_top p
  rw [← hcoord]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨x.1.1, x.2⟩, ?_⟩
  simp [quotientPlacement, x.1.2]

/-- Mapping the universal coefficient placement to the quotient function
field gives `quotientPlacement` exactly. -/
theorem map_coefficientPlacement_eq_quotientPlacement
    {V : Type*} [DecidableEq V] (root : V)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime]
    (v : V) (i : Fin 3) :
    algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
        (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
      (Ideal.Quotient.mk p (coefficientPlacement root v i)) =
      quotientPlacement root p v i := by
  by_cases hv : v = root
  · simp [coefficientPlacement, quotientPlacement, hv]
  · simp [coefficientPlacement, quotientPlacement,
      FractionQuotientCoordinates.coordinate, hv]

/-- One occurrence row maps coefficientwise to the same row evaluated at
the quotient placement. -/
theorem map_occurrenceDirectionRow
    {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) (e : E)
    (p : Ideal (MvPolynomial (SpatialVariable root) ℚ)) [p.IsPrime]
    (x : SpatialVariable root) :
    algebraMap (MvPolynomial (SpatialVariable root) ℚ ⧸ p)
        (FractionRing (MvPolynomial (SpatialVariable root) ℚ ⧸ p))
      (Ideal.Quotient.mk p
        (occurrenceDirectionRow root src dst
          (coefficientPlacement (k := ℚ) root) e x)) =
      occurrenceDirectionRow root src dst
        (quotientPlacement root p) e x := by
  by_cases hs : src e = x.1.1 <;>
    by_cases hd : dst e = x.1.1 <;>
    simp [occurrenceDirectionRow, hs, hd,
      map_coefficientPlacement_eq_quotientPlacement] <;> rfl

/-- An occurrence row depends only on its unoriented active edge. -/
theorem occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
    {k V E : Type*} [Field k] [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (a : V → Fin 3 → k) (e : active) (f : SimpleEdge V)
    (hef : SparseNullIncidence.activeEdge src dst active hLoop e = f) :
    occurrenceDirectionRow root src dst a e.1 =
      GroundedDirectionConstraint.groundedDirectionRow root a f := by
  have hpair : s(f.source, f.target) = s(src e.1, dst e.1) := by
    rw [f.source_target_mk, ← hef]
    rfl
  rcases Sym2.eq_iff.mp hpair with h | h
  · funext x
    simp [occurrenceDirectionRow,
      GroundedDirectionConstraint.groundedDirectionRow,
      DirectionStress.directionRow, DirectionStress.edgeDirection,
      h.1, h.2]
  · funext x
    simp [occurrenceDirectionRow,
      GroundedDirectionConstraint.groundedDirectionRow,
      DirectionStress.directionRow, DirectionStress.edgeDirection,
      h.1, h.2]
    ring

/-- For the canonical skeleton selection, the selected occurrence-row set
is exactly the grounded direction-row set of the skeleton. -/
theorem range_selectedOccurrenceRows_eq_range_groundedDirectionRows
    {k V E : Type*} [Field k] [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (a : V → Fin 3 → k) :
    Set.range (fun e : SelectedOccurrence active
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented) ↦
      occurrenceDirectionRow root src dst a e.1.1) =
    Set.range (fun f : F ↦
      GroundedDirectionConstraint.groundedDirectionRow root a f.1) := by
  ext row
  constructor
  · rintro ⟨e, rfl⟩
    let f : F := ⟨SparseNullIncidence.activeEdge
      src dst active hLoop e.1,
      SparseNullIncidence.activeEdge_mem_of_mem_selectedSkeletonOccurrences
        src dst active hLoop F hRepresented e.1 e.2⟩
    refine ⟨f, ?_⟩
    exact (occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
      root src dst active hLoop a e.1 f.1 rfl).symm
  · rintro ⟨f, rfl⟩
    let e : SelectedOccurrence active
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented) :=
      ⟨SparseNullIncidence.representedOccurrence
          src dst active hLoop F hRepresented f,
        SparseNullIncidence.representedOccurrence_mem_selectedSkeletonOccurrences
          src dst active hLoop F hRepresented f⟩
    refine ⟨e, ?_⟩
    exact occurrenceDirectionRow_eq_groundedDirectionRow_of_activeEdge_eq
      root src dst active hLoop a e.1 f.1
        (SparseNullIncidence.representedOccurrence_activeEdge
          src dst active hLoop F hRepresented f)

end

end SelectedDirectionFibre

end RB31E2E
