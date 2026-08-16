import RB31EndToEnd.NullCellule.SelectedNullHeightPrimewise
import RB31EndToEnd.Incidence.FiniteFullProvenancePropernessAssembly

/-!
# End-to-end assembly from grounded PF semismallness

All algebraic-geometric, provenance, localization, elimination, and
rigidity interfaces are discharged here.  The sole input is the grounded
PF function-field semismallness theorem for sparse simple edge systems.
-/

namespace RB31E2E

noncomputable section

open UniversalHomogeneousChart

universe u v

/-- One finite complete-provenance chart satisfies the exact generic prime
height condition directly from grounded PF semismallness. -/
theorem finiteGenericIncidenceProvenancePrimeHeightCondition_of_groundedPF
    {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V)
    (hcard : F.card =
      6 * (Fintype.card V - 1) - 2 * active.card)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (GroundedTwistSplit.SpatialVariable root)) :
    FiniteGenericIncidenceProvenancePrimeHeightCondition
      root src dst active hLoop angularChart
        (SparseNullIncidence.selectedSkeletonOccurrences
          src dst active hLoop F hRepresented)
        distinctChart := by
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  apply
    PinOuterFullProvenanceHeightTransfer.finiteGenericIncidenceProvenancePrimeHeightCondition_of_incidenceLocalizedSelectedNullIdeal_height
      root src dst active hLoop angularChart selected distinctChart
  · dsimp [selected]
    rw [SparseNullIncidence.card_selectedSkeletonOccurrences]
    exact hcard
  · exact
      SelectedNullHeightPrimewise.incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
        root src dst active hLoop F hRepresented angularChart distinctChart hPF

/-- Grounded semismallness for every sparse simple edge system implies the
body--pin theorem. -/
theorem endToEndBodyPinStatement_of_groundedPF
    (hPF : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (F : SimpleEdgeSet V), Sparse22 F →
      ∀ (root : V) {K : Type} [Field K] [Algebra ℚ K]
        (a : V → Fin 3 → K),
        a root = 0 →
        Function.Injective a →
        IntermediateField.adjoin ℚ
            (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
        DirectionStress.directionStressDim F a +
            (Algebra.trdeg ℚ K).toNat ≤
          Nat.card (GroundedTwistSplit.SpatialVariable root)) :
    EndToEndBodyPinStatement := by
  apply endToEndBodyPinStatement_of_finiteGenericFullProvenancePrimeHeights
  intro V E _instFV _instDV _instFE _instDE
    src dst active hLoop F _hTwo hSparse hRepresented hcard
    root distinctChart angularChart
  exact finiteGenericIncidenceProvenancePrimeHeightCondition_of_groundedPF
    root src dst active hLoop F hRepresented angularChart
      distinctChart hcard (hPF V F hSparse root)

end

end RB31E2E
