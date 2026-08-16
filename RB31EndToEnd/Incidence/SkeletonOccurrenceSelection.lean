import RB31EndToEnd.Incidence.UniversalChartHeightElimination

/-!
# Selecting provenance occurrences for a sparse skeleton

The properness input says that every simple skeleton edge is represented by
an actual active pin occurrence.  This file makes one such choice for every
edge and proves that the choice is automatically injective: a single
occurrence has only one unordered endpoint edge.  Consequently the selected
occurrence finset has exactly the skeleton cardinality required by the
universal chart budget.

No rigidity, height, elimination, or choice-independent mathematical claim is
assumed.  Classical choice is used only to select the already supplied finite
provenance witnesses.
-/

namespace RB31E2E

namespace SparseNullIncidence

noncomputable section

/-- Choose one actual active occurrence representing each skeleton edge. -/
def representedOccurrence
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) : active :=
  Classical.choose (hRepresented f.1 f.2)

/-- The chosen occurrence retains the exact simple-edge provenance. -/
theorem representedOccurrence_activeEdge
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) :
    activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented f) = f.1 :=
  Classical.choose_spec (hRepresented f.1 f.2)

/-- Distinct skeleton edges select distinct active occurrences. -/
theorem representedOccurrence_injective
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) :
    Function.Injective
      (representedOccurrence src dst active hLoop F hRepresented) := by
  intro f g hfg
  apply Subtype.ext
  calc
    f.1 = activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented f) :=
      (representedOccurrence_activeEdge
        src dst active hLoop F hRepresented f).symm
    _ = activeEdge src dst active hLoop
        (representedOccurrence src dst active hLoop F hRepresented g) := by
      rw [hfg]
    _ = g.1 := representedOccurrence_activeEdge
      src dst active hLoop F hRepresented g

/-- The actual active occurrences selected by the skeleton, with their
occurrence labels retained. -/
def selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) : Finset active :=
  Finset.univ.image
    (representedOccurrence src dst active hLoop F hRepresented)

theorem representedOccurrence_mem_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : F) :
    representedOccurrence src dst active hLoop F hRepresented f ∈
      selectedSkeletonOccurrences src dst active hLoop F hRepresented := by
  simp [selectedSkeletonOccurrences]

/-- The selected occurrence family has exactly one member per skeleton edge. -/
theorem card_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) :
    (selectedSkeletonOccurrences
      src dst active hLoop F hRepresented).card = F.card := by
  rw [selectedSkeletonOccurrences,
    Finset.card_image_of_injective Finset.univ
      (representedOccurrence_injective
        src dst active hLoop F hRepresented)]
  simp

/-- Every skeleton edge is represented by a member of the selected finset. -/
theorem exists_selectedOccurrence_activeEdge_eq
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (f : SimpleEdge V) (hf : f ∈ F) :
    ∃ e : selectedSkeletonOccurrences
        src dst active hLoop F hRepresented,
      activeEdge src dst active hLoop e.1 = f := by
  let fF : F := ⟨f, hf⟩
  refine ⟨
    ⟨representedOccurrence src dst active hLoop F hRepresented fF,
      representedOccurrence_mem_selectedSkeletonOccurrences
        src dst active hLoop F hRepresented fF⟩, ?_⟩
  exact representedOccurrence_activeEdge
    src dst active hLoop F hRepresented fF

/-- Conversely, every selected occurrence comes from an edge of the given
skeleton; the selection introduces no auxiliary null equation. -/
theorem activeEdge_mem_of_mem_selectedSkeletonOccurrences
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (e : active)
    (he : e ∈ selectedSkeletonOccurrences
      src dst active hLoop F hRepresented) :
    activeEdge src dst active hLoop e ∈ F := by
  rw [selectedSkeletonOccurrences] at he
  obtain ⟨f, _hf, hfe⟩ := Finset.mem_image.mp he
  subst e
  rw [representedOccurrence_activeEdge
    src dst active hLoop F hRepresented f]
  exact f.2

/-- The exact sparse-null skeleton count transfers verbatim to the universal
chart generator budget, while retaining one actual occurrence as provenance
for every selected null equation. -/
theorem selectedSkeletonUniversalChartGenerator_budget
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f)
    (chart : active → Fin 3)
    (hcard : F.card =
      6 * (Fintype.card V - 1) - 2 * active.card) :
    UniversalHomogeneousChart.groundedTwistVariableCount root ≤
      Fintype.card
          (UniversalHomogeneousChart.ActiveCompatibilityIndex active chart) +
        (selectedSkeletonOccurrences
          src dst active hLoop F hRepresented).card := by
  apply UniversalHomogeneousChart.universalChartGenerator_budget
  rw [card_selectedSkeletonOccurrences]
  exact hcard

end

end SparseNullIncidence

end RB31E2E
