import RB31EndToEnd.Combinatorics.ProvenanceFlag
import RB31EndToEnd.Combinatorics.ProvenanceFlagArithmetic
import RB31EndToEnd.Combinatorics.Sparse22.GraphExtension

/-!
# The terminal hyperforest forced by a sparse provenance completion

For one active flag, the restored terminal triangle together with its
private ghost star is a literal completed `K₄`.  This file derives, rather
than assumes, the two combinatorial consequences needed by the provenance
induction:

* distinct terminal triples meet in at most one live vertex;
* every nonempty family of `j` flags uses at least `2*j+1` live terminals.

The proof uses the actual finite edge and vertex unions.  In particular, the
six-edge count and pairwise edge-disjointness are proved as `Finset`
identities; no forest or counting conclusion is stored in `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

private def liveVertexEmbedding : V ↪ V ⊕ Flag where
  toFun := Sum.inl
  inj' := Sum.inl_injective

private def ghostVertexEmbedding : Flag ↪ V ⊕ Flag where
  toFun := Sum.inr
  inj' := Sum.inr_injective

/-! ## One completed flag -/

/-- The three live terminals of `t`, together with its private ghost. -/
def State.flagVertices (S : State V Flag) (t : Flag) : Finset (V ⊕ Flag) :=
  insert (Sum.inr t) ((S.terminals t).map liveVertexEmbedding)

/-- The actual completion edges supported on one flag's four vertices. -/
def State.flagCompletedEdges (S : State V Flag) (t : Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  edgesInside S.completionEdges (S.flagVertices t)

@[simp]
theorem State.mem_flagVertices_live (S : State V Flag) (t : Flag) (v : V) :
    Sum.inl v ∈ S.flagVertices t ↔ v ∈ S.terminals t := by
  simp [State.flagVertices, liveVertexEmbedding]

@[simp]
theorem State.mem_flagVertices_ghost (S : State V Flag) (t u : Flag) :
    Sum.inr u ∈ S.flagVertices t ↔ u = t := by
  simp [State.flagVertices, liveVertexEmbedding]

theorem State.flagVertices_nonempty (S : State V Flag) (t : Flag) :
    (S.flagVertices t).Nonempty :=
  ⟨Sum.inr t, by simp⟩

@[simp]
theorem State.card_flagVertices (S : State V Flag) (t : Flag) :
    (S.flagVertices t).card = 4 := by
  rw [State.flagVertices, Finset.card_insert_of_notMem]
  · rw [Finset.card_map, S.terminals_card t]
  · simp [liveVertexEmbedding]

/-- Every terminal pair of a flag is present after completion: it is either
the distinguished restored edge or one of the two live terminal edges. -/
theorem State.lifted_terminalEdge_mem_completionEdges
    (S : State V Flag) (t : Flag) {a b : V}
    (ha : a ∈ S.terminals t) (hb : b ∈ S.terminals t) (hab : a ≠ b) :
    liftLiveEdge (Flag := Flag) (simpleEdge a b hab) ∈ S.completionEdges := by
  let e : SimpleEdge V := simpleEdge a b hab
  have heSupported : e.vertices ⊆ S.terminals t := by
    rw [show e = simpleEdge a b hab from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  by_cases heMissing : e = S.missing t
  · rw [show simpleEdge a b hab = e from rfl, heMissing]
    exact S.lifted_missing_mem_completionEdges t
  · apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact S.other_terminal_edges_live t e heSupported heMissing

/-- Every active flag gives named vertices for a genuine `K₄` in the
literal completion. -/
theorem State.exists_namedK4Witness_completion
    (S : State V Flag) (t : Flag) :
    ∃ a b c : V,
      S.terminals t = {a, b, c} ∧
      NamedK4Witness S.completionEdges
        (Sum.inr t) (Sum.inl a) (Sum.inl b) (Sum.inl c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hterm⟩ :=
    Finset.card_eq_three.mp (S.terminals_card t)
  have ha : a ∈ S.terminals t := by rw [hterm]; simp
  have hb : b ∈ S.terminals t := by rw [hterm]; simp
  have hc : c ∈ S.terminals t := by rw [hterm]; simp
  have hab' : Sum.inl a ≠ (Sum.inl b : V ⊕ Flag) := by
    exact fun h ↦ hab (Sum.inl.inj h)
  have hac' : Sum.inl a ≠ (Sum.inl c : V ⊕ Flag) := by
    exact fun h ↦ hac (Sum.inl.inj h)
  have hbc' : Sum.inl b ≠ (Sum.inl c : V ⊕ Flag) := by
    exact fun h ↦ hbc (Sum.inl.inj h)
  refine ⟨a, b, c, hterm, ?_⟩
  refine
    { hva := by simp
      hvb := by simp
      hvc := by simp
      hab := hab'
      hac := hac'
      hbc := hbc'
      va_mem := ?_
      vb_mem := ?_
      vc_mem := ?_
      ab_mem := ?_
      ac_mem := ?_
      bc_mem := ?_ }
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t ha
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t hb
  · simpa [ghostEdge, simpleEdge] using S.ghostEdge_mem_completionEdges t hc
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t ha hb hab
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t ha hc hac
  · simpa [liftLiveEdge, simpleEdge] using
      S.lifted_terminalEdge_mem_completionEdges t hb hc hbc

/-- The four vertices of an active flag are tight in every sparse
completion. -/
theorem State.flagVertices_tight
    (S : State V Flag) (hSparse : S.CompletionSparse) (t : Flag) :
    Tight22 S.completionEdges (S.flagVertices t) := by
  obtain ⟨a, b, c, hterm, hK⟩ := S.exists_namedK4Witness_completion t
  have hTight := tight22_namedK4Vertices hSparse hK
  simpa [State.flagVertices, namedK4Vertices, hterm, liveVertexEmbedding] using hTight

/-- A single flag contributes exactly the six edges of its completed
`K₄`. -/
@[simp]
theorem State.card_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) (t : Flag) :
    (S.flagCompletedEdges t).card = 6 := by
  have hTight := S.flagVertices_tight hSparse t
  rw [State.flagCompletedEdges, hTight.2, S.card_flagVertices]

theorem State.flagCompletedEdges_subset_completionEdges
    (S : State V Flag) (t : Flag) :
    S.flagCompletedEdges t ⊆ S.completionEdges :=
  edgesInside_subset _ _

/-! ## A small simple-graph cardinal bound -/

private def endpointIntoSubset
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) : e.vertices ↪ X where
  toFun x := ⟨x.1, he x.2⟩
  inj' := by
    intro x y hxy
    exact Subtype.ext (Subtype.mk.inj hxy)

private def restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) : Finset X :=
  e.vertices.attach.map (endpointIntoSubset X e he)

@[simp]
private theorem card_restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) :
    (restrictedEdgeVertices X e he).card = 2 := by
  simp [restrictedEdgeVertices, e.card_vertices]

private theorem map_restrictedEdgeVertices
    {A : Type*} [DecidableEq A] (X : Finset A) (e : SimpleEdge A)
    (he : e.vertices ⊆ X) :
    (restrictedEdgeVertices X e he).map
        ⟨Subtype.val, Subtype.val_injective⟩ = e.vertices := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx
    obtain ⟨z, _hz, hza⟩ := Finset.mem_map.mp ha
    have hzval : z.1 = x :=
      (congrArg Subtype.val hza).trans hax
    exact hzval ▸ z.2
  · intro hx
    let z : e.vertices := ⟨x, hx⟩
    let a : X := ⟨x, he hx⟩
    apply Finset.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨z, by simp [z], rfl⟩

private def edgesInsideToTwoSubsets
    {A : Type*} [DecidableEq A] (F : SimpleEdgeSet A) (X : Finset A) :
    (↑(edgesInside F X)) ↪
      (↑((Finset.univ : Finset X).powersetCard 2)) where
  toFun e :=
    ⟨restrictedEdgeVertices X e.1 (mem_edgesInside.mp e.2).2, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, card_restrictedEdgeVertices _ _ _⟩⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply SimpleEdge.eq_of_vertices_eq
    have hmap := congrArg
      (fun Y : Finset X ↦ Y.map ⟨Subtype.val, Subtype.val_injective⟩)
      (Subtype.mk.inj hef)
    simpa [map_restrictedEdgeVertices] using hmap

/-- A simple graph induced on `X` has at most `X.card.choose 2` edges. -/
theorem card_edgesInside_le_choose_two
    {A : Type*} [DecidableEq A] (F : SimpleEdgeSet A) (X : Finset A) :
    (edgesInside F X).card ≤ X.card.choose 2 := by
  let emb := edgesInsideToTwoSubsets F X
  have hcard := Fintype.card_le_of_injective emb emb.injective
  calc
    (edgesInside F X).card ≤
        ((Finset.univ : Finset X).powersetCard 2).card := by
      simpa only [Fintype.card_coe] using hcard
    _ = (Finset.univ : Finset X).card.choose 2 :=
      Finset.card_powersetCard 2 (Finset.univ : Finset X)
    _ = X.card.choose 2 := by simp

/-- A `(2,2)`-tight vertex set with at least two vertices has at least four
vertices.  The exclusion of sizes two and three uses the actual simple-edge
bound above. -/
theorem four_le_card_of_tight22
    {A : Type*} [DecidableEq A] {F : SimpleEdgeSet A} {X : Finset A}
    (hTight : Tight22 F X) (hTwo : 2 ≤ X.card) :
    4 ≤ X.card := by
  have hBound := card_edgesInside_le_choose_two F X
  rw [hTight.2] at hBound
  by_contra hFour
  have hCases : X.card = 2 ∨ X.card = 3 := by omega
  rcases hCases with hTwoEq | hThreeEq
  · rw [hTwoEq] at hBound
    norm_num at hBound
  · rw [hThreeEq] at hBound
    norm_num at hBound

/-! ## Distinct flags meet in at most one terminal -/

theorem State.flagVertices_inter_eq
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    S.flagVertices t ∩ S.flagVertices u =
      (S.terminals t ∩ S.terminals u).map liveVertexEmbedding := by
  ext x
  cases x with
  | inl v =>
      simp only [Finset.mem_inter, State.mem_flagVertices_live,
        Finset.mem_map]
      constructor
      · rintro ⟨hvt, hvu⟩
        exact ⟨v, ⟨hvt, hvu⟩, rfl⟩
      · rintro ⟨a, ha, hav⟩
        have hav' : a = v := Sum.inl.inj hav
        subst a
        exact ha
  | inr w =>
      simp only [Finset.mem_inter, State.mem_flagVertices_ghost,
        Finset.mem_map]
      constructor
      · rintro ⟨hwt, hwu⟩
        exact (htu (hwt.symm.trans hwu)).elim
      · rintro ⟨a, _ha, haw⟩
        change (Sum.inl a : V ⊕ Flag) = Sum.inr w at haw
        exact (Sum.inl_ne_inr haw).elim

theorem State.card_flagVertices_inter
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    (S.flagVertices t ∩ S.flagVertices u).card =
      (S.terminals t ∩ S.terminals u).card := by
  rw [S.flagVertices_inter_eq htu, Finset.card_map]

/-- Completion sparsity forbids two distinct flags from sharing two live
terminals. -/
theorem State.card_terminal_inter_le_one
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {t u : Flag} (htu : t ≠ u) :
    (S.terminals t ∩ S.terminals u).card ≤ 1 := by
  by_contra hOne
  have hTwo : 2 ≤ (S.terminals t ∩ S.terminals u).card := by omega
  have hInterNonempty : (S.flagVertices t ∩ S.flagVertices u).Nonempty := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (S.terminals t ∩ S.terminals u).card)
    refine ⟨Sum.inl v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact S.mem_flagVertices_live t v |>.2 (Finset.mem_inter.mp hv).1
    · exact S.mem_flagVertices_live u v |>.2 (Finset.mem_inter.mp hv).2
  have hInterTight :=
    (tight22_union_inter hSparse
      (S.flagVertices_tight hSparse t)
      (S.flagVertices_tight hSparse u) hInterNonempty).2
  have hInterTwo : 2 ≤ (S.flagVertices t ∩ S.flagVertices u).card := by
    rw [S.card_flagVertices_inter htu]
    exact hTwo
  have hFour := four_le_card_of_tight22 hInterTight hInterTwo
  rw [S.card_flagVertices_inter htu] at hFour
  have hAtMostThree : (S.terminals t ∩ S.terminals u).card ≤ 3 := by
    calc
      (S.terminals t ∩ S.terminals u).card ≤ (S.terminals t).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := S.terminals_card t
  omega

/-- The six-edge packets of distinct flags are disjoint, now as a derived
fact about the literal edge sets. -/
theorem State.disjoint_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {t u : Flag} (htu : t ≠ u) :
    Disjoint (S.flagCompletedEdges t) (S.flagCompletedEdges u) := by
  rw [Finset.disjoint_left]
  intro e het heu
  have heSubset : e.vertices ⊆ S.flagVertices t ∩ S.flagVertices u :=
    Finset.subset_inter (mem_edgesInside.mp het).2 (mem_edgesInside.mp heu).2
  have hCard := Finset.card_le_card heSubset
  rw [e.card_vertices, S.card_flagVertices_inter htu] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

/-! ## Exact unions and the terminal hyperforest inequality -/

/-- Live terminals used by a finite family of flags. -/
def State.terminalUnion (S : State V Flag) (A : Finset Flag) : Finset V :=
  A.biUnion S.terminals

/-- All live terminals and all private ghosts used by `A`. -/
def State.flagVertexUnion (S : State V Flag) (A : Finset Flag) :
    Finset (V ⊕ Flag) :=
  (S.terminalUnion A).map liveVertexEmbedding ∪
    A.map ghostVertexEmbedding

/-- Union of the actual six-edge packets belonging to `A`. -/
def State.flagEdgeUnion (S : State V Flag) (A : Finset Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  A.biUnion S.flagCompletedEdges

theorem State.flagVertices_subset_flagVertexUnion
    (S : State V Flag) {A : Finset Flag} {t : Flag} (ht : t ∈ A) :
    S.flagVertices t ⊆ S.flagVertexUnion A := by
  intro x hx
  cases x with
  | inl v =>
      have hv : v ∈ S.terminals t := (S.mem_flagVertices_live t v).1 hx
      apply Finset.mem_union_left
      exact Finset.mem_map.mpr
        ⟨v, Finset.mem_biUnion.mpr ⟨t, ht, hv⟩, rfl⟩
  | inr u =>
      have hut : u = t := (S.mem_flagVertices_ghost t u).1 hx
      subst u
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨t, ht, rfl⟩

theorem State.card_flagVertexUnion (S : State V Flag) (A : Finset Flag) :
    (S.flagVertexUnion A).card = (S.terminalUnion A).card + A.card := by
  have hDisjoint :
      Disjoint ((S.terminalUnion A).map liveVertexEmbedding)
        (A.map ghostVertexEmbedding) := by
    rw [Finset.disjoint_left]
    intro x hxLive hxGhost
    obtain ⟨v, _hv, hvx⟩ := Finset.mem_map.mp hxLive
    obtain ⟨t, _ht, htx⟩ := Finset.mem_map.mp hxGhost
    have hbad : (Sum.inl v : V ⊕ Flag) = Sum.inr t := hvx.trans htx.symm
    exact Sum.inl_ne_inr hbad
  rw [State.flagVertexUnion, Finset.card_union_of_disjoint hDisjoint,
    Finset.card_map, Finset.card_map]

theorem State.pairwiseDisjoint_flagCompletedEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) (A : Finset Flag) :
    (A : Set Flag).PairwiseDisjoint S.flagCompletedEdges := by
  intro t _ht u _hu htu
  exact S.disjoint_flagCompletedEdges hSparse htu

theorem State.card_flagEdgeUnion
    (S : State V Flag) (hSparse : S.CompletionSparse) (A : Finset Flag) :
    (S.flagEdgeUnion A).card = 6 * A.card := by
  rw [State.flagEdgeUnion,
    Finset.card_biUnion (S.pairwiseDisjoint_flagCompletedEdges hSparse A)]
  simp [S.card_flagCompletedEdges hSparse, Nat.mul_comm]

theorem State.flagEdgeUnion_subset_completionEdges
    (S : State V Flag) (A : Finset Flag) :
    S.flagEdgeUnion A ⊆ S.completionEdges := by
  intro e he
  obtain ⟨t, _ht, het⟩ := Finset.mem_biUnion.mp he
  exact S.flagCompletedEdges_subset_completionEdges t het

theorem State.flagEdgeUnion_supported
    (S : State V Flag) (A : Finset Flag) :
    SupportedOn (S.flagEdgeUnion A) (S.flagVertexUnion A) := by
  intro e he
  obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
  exact (mem_edgesInside.mp het).2.trans
    (S.flagVertices_subset_flagVertexUnion ht)

theorem State.flagEdgeUnion_subset_edgesInside
    (S : State V Flag) (A : Finset Flag) :
    S.flagEdgeUnion A ⊆ edgesInside S.completionEdges (S.flagVertexUnion A) := by
  intro e he
  exact mem_edgesInside.mpr
    ⟨S.flagEdgeUnion_subset_completionEdges A he,
      S.flagEdgeUnion_supported A he⟩

/-- The incidence ledger has exactly three terminal occurrences per flag. -/
theorem State.sum_card_terminals
    (S : State V Flag) (A : Finset Flag) :
    (∑ t ∈ A, (S.terminals t).card) = 3 * A.card := by
  simp [S.terminals_card, Nat.mul_comm]

/-- Every nonempty family of `j` active flags uses at least `2*j+1`
distinct live terminals. -/
theorem State.two_mul_card_add_one_le_card_terminalUnion
    (S : State V Flag) (hSparse : S.CompletionSparse)
    {A : Finset Flag} (hA : A.Nonempty) :
    2 * A.card + 1 ≤ (S.terminalUnion A).card := by
  have hVertexNonempty : (S.flagVertexUnion A).Nonempty := by
    obtain ⟨t, ht⟩ := hA
    exact ⟨Sum.inr t,
      S.flagVertices_subset_flagVertexUnion ht (by simp)⟩
  have hSparseUpper := hSparse (S.flagVertexUnion A) hVertexNonempty
  have hEdgeLower := Finset.card_le_card
    (S.flagEdgeUnion_subset_edgesInside A)
  have hEdgeCard := S.card_flagEdgeUnion hSparse A
  have hVertexCard := S.card_flagVertexUnion A
  have hPositive : 1 ≤ (S.terminalUnion A).card + A.card := by
    rw [← hVertexCard]
    exact Finset.card_pos.mpr hVertexNonempty
  have hArithmetic :
      6 * A.card + 2 ≤
        2 * ((S.terminalUnion A).card + A.card) := by
    rw [hEdgeCard] at hEdgeLower
    rw [hVertexCard] at hSparseUpper
    omega
  exact terminal_count_ge_two_mul_add_one
    (Finset.card_pos.mpr hA) hArithmetic

/-- Derived hyperforest property of the terminal triples.  This definition
is only an abbreviation for the quantified Finset inequality; it is never a
field of `State` and the theorem below constructs it from completion
sparsity. -/
def State.TerminalHyperforest (S : State V Flag) : Prop :=
  ∀ A : Finset Flag, A.Nonempty → 2 * A.card + 1 ≤ (S.terminalUnion A).card

theorem State.terminalHyperforest
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.TerminalHyperforest := by
  intro A hA
  exact S.two_mul_card_add_one_le_card_terminalUnion hSparse hA

end ProvenanceFlag

end

end RB31E2E
