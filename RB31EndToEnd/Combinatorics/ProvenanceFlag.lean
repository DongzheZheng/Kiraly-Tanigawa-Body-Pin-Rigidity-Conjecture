import RB31EndToEnd.Combinatorics.Sparse22.Construction

/-!
# Provenance-carrying collinearity flags

This file introduces the finite combinatorial state used by the
provenance-flag induction.  The vertex type `V` is exactly the type of live
vertices and the type `Flag` is exactly the type of active flags.  Thus no
ambient labels, inactive flags, or support predicates occur in the state.

Every flag records three live terminals, one missing terminal edge, and one
private ghost vertex.  The completion restores the missing edge and joins
the ghost to the three terminals.  Its vertex type is literally
`V ⊕ Flag`.

No semismallness or height conclusion is stored in the structure.  The
combinatorial hypothesis used later is the transparent proposition that the
actual completed edge set is `(2,2)`-sparse.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Transporting live edges to the completed vertex type -/

/-- A live simple edge transported along the left injection into
`V ⊕ Flag`. -/
def liftLiveEdge (e : SimpleEdge V) : SimpleEdge (V ⊕ Flag) :=
  ⟨e.1.map Sum.inl, by
    rw [Sym2.isDiag_map Sum.inl_injective]
    exact e.2⟩

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem liftLiveEdge_val (e : SimpleEdge V) :
    (liftLiveEdge (Flag := Flag) e).1 = e.1.map Sum.inl := rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
theorem liftLiveEdge_injective :
    Function.Injective (liftLiveEdge (V := V) (Flag := Flag)) := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Sum.inl_injective (Subtype.mk.inj hef)

/-- The embedding version used by `Finset.map`. -/
def liftLiveEdgeEmbedding : SimpleEdge V ↪ SimpleEdge (V ⊕ Flag) where
  toFun := liftLiveEdge
  inj' := liftLiveEdge_injective

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
@[simp]
theorem mem_map_liftLiveEdgeEmbedding
    {F : SimpleEdgeSet V} {e : SimpleEdge V} :
    liftLiveEdge (Flag := Flag) e ∈
        F.map (liftLiveEdgeEmbedding (V := V) (Flag := Flag)) ↔
      e ∈ F := by
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
    have : f = e := liftLiveEdge_injective hfe
    simpa [this] using hf
  · intro he
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩

/-- The private ghost-to-terminal edge belonging to one active flag. -/
def ghostEdge (t : Flag) (v : V) : SimpleEdge (V ⊕ Flag) :=
  simpleEdge (Sum.inr t) (Sum.inl v) (by simp)

omit [Fintype V] [Fintype Flag] in
@[simp]
theorem vertices_ghostEdge (t : Flag) (v : V) :
    (ghostEdge t v).vertices = {Sum.inr t, Sum.inl v} := by
  simp [ghostEdge]

/-! ## Flag states and their literal completion -/

/--
Finite provenance-flag data on a live simple graph.

`V` contains exactly the live vertices and `Flag` contains exactly the
active flags.  Consequently every edge and terminal label is active by its
type.  Each terminal set has three elements; `missing t` is one of its three
pairs and is absent from the live graph; every other terminal pair is live.
-/
structure State (V Flag : Type*)
    [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] where
  edges : SimpleEdgeSet V
  terminals : Flag → Finset V
  missing : Flag → SimpleEdge V
  terminals_card : ∀ t, (terminals t).card = 3
  missing_supported : ∀ t, (missing t).vertices ⊆ terminals t
  missing_not_live : ∀ t, missing t ∉ edges
  other_terminal_edges_live :
    ∀ t, ∀ e : SimpleEdge V,
      e.vertices ⊆ terminals t → e ≠ missing t → e ∈ edges

/-- Live edges, transported to the completed vertex type. -/
def State.liftedLiveEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  S.edges.map (liftLiveEdgeEmbedding (V := V) (Flag := Flag))

/-- The restored distinguished terminal edge of every active flag. -/
def State.restoredMissingEdges (S : State V Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  Finset.univ.image fun t ↦ liftLiveEdge (Flag := Flag) (S.missing t)

/-- All private ghost stars, one for every inhabitant of `Flag`. -/
def State.ghostStarEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  Finset.univ.biUnion fun t ↦
    (S.terminals t).image fun v ↦ ghostEdge t v

/-- The literal completed edge set: restore one terminal edge and attach
one private three-star for every active flag. -/
def State.completionEdges (S : State V Flag) : SimpleEdgeSet (V ⊕ Flag) :=
  S.liftedLiveEdges ∪ S.restoredMissingEdges ∪ S.ghostStarEdges

/-- Sparsity of the actual completed edge set. -/
def State.CompletionSparse (S : State V Flag) : Prop :=
  Sparse22 S.completionEdges

@[simp]
theorem State.mem_liftedLiveEdges (S : State V Flag) (e : SimpleEdge V) :
    liftLiveEdge (Flag := Flag) e ∈ S.liftedLiveEdges ↔ e ∈ S.edges := by
  exact mem_map_liftLiveEdgeEmbedding

theorem State.liftedLiveEdges_subset_completionEdges (S : State V Flag) :
    S.liftedLiveEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_union_left _ he)

theorem State.restoredMissingEdges_subset_completionEdges (S : State V Flag) :
    S.restoredMissingEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_union_right _ he)

theorem State.ghostStarEdges_subset_completionEdges (S : State V Flag) :
    S.ghostStarEdges ⊆ S.completionEdges := by
  intro e he
  exact Finset.mem_union_right _ he

/-- Every active flag's restored missing edge is present in the completion. -/
theorem State.lifted_missing_mem_completionEdges
    (S : State V Flag) (t : Flag) :
    liftLiveEdge (Flag := Flag) (S.missing t) ∈ S.completionEdges := by
  apply S.restoredMissingEdges_subset_completionEdges
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩

/-- Every ghost-terminal incidence is present in the completion. -/
theorem State.ghostEdge_mem_completionEdges
    (S : State V Flag) (t : Flag) {v : V} (hv : v ∈ S.terminals t) :
    ghostEdge t v ∈ S.completionEdges := by
  apply S.ghostStarEdges_subset_completionEdges
  exact Finset.mem_biUnion.mpr
    ⟨t, Finset.mem_univ t, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-- Completion sparsity immediately restricts to the transported live graph. -/
theorem State.completionSparse_mono_live (S : State V Flag)
    (hS : S.CompletionSparse) : Sparse22 S.liftedLiveEdges := by
  exact hS.mono S.liftedLiveEdges_subset_completionEdges

end ProvenanceFlag

end

end RB31E2E
