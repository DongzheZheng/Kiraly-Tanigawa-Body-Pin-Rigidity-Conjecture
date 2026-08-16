import RB31EndToEnd.Combinatorics.ProvenanceFlagForest

/-!
# A derived low-degree selection lemma for provenance flags

This file partitions the exact live vertex type into vertices contained in
zero, one, or at least two active flags.  It then proves the three ledgers
used by the provenance induction from the literal `State` data:

* the completion has `|E| + 4 * |Flag|` edges;
* the terminal incidence sum is `3 * |Flag|`;
* the live degree sum is `2 * |E|`.

Together with completion sparsity and the terminal-hyperforest overlap
theorem, these identities force either an outside vertex of live degree at
most three or a private terminal of live degree at most two.  The selection
conclusion is a theorem, not a field of `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-! ## Flag multiplicity and the exact live-vertex partition -/

/-- Active flags containing a live vertex. -/
def State.activeFlagsAt (S : State V Flag) (v : V) : Finset Flag :=
  Finset.univ.filter fun t ↦ v ∈ S.terminals t

/-- Number of active flags containing a live vertex. -/
def State.flagMultiplicity (S : State V Flag) (v : V) : ℕ :=
  (S.activeFlagsAt v).card

/-- Live vertices outside every active flag. -/
def State.outsideVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ S.flagMultiplicity v = 0

/-- Live vertices belonging to exactly one active flag. -/
def State.privateVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ S.flagMultiplicity v = 1

/-- Live vertices belonging to at least two active flags. -/
def State.sharedVertices (S : State V Flag) : Finset V :=
  Finset.univ.filter fun v ↦ 2 ≤ S.flagMultiplicity v

/-- Total flag incidence carried by shared live vertices. -/
def State.sharedIncidence (S : State V Flag) : ℕ :=
  ∑ v ∈ S.sharedVertices, S.flagMultiplicity v

@[simp]
theorem State.mem_activeFlagsAt (S : State V Flag) (v : V) (t : Flag) :
    t ∈ S.activeFlagsAt v ↔ v ∈ S.terminals t := by
  simp [State.activeFlagsAt]

@[simp]
theorem State.mem_outsideVertices (S : State V Flag) (v : V) :
    v ∈ S.outsideVertices ↔ S.flagMultiplicity v = 0 := by
  simp [State.outsideVertices]

@[simp]
theorem State.mem_privateVertices (S : State V Flag) (v : V) :
    v ∈ S.privateVertices ↔ S.flagMultiplicity v = 1 := by
  simp [State.privateVertices]

@[simp]
theorem State.mem_sharedVertices (S : State V Flag) (v : V) :
    v ∈ S.sharedVertices ↔ 2 ≤ S.flagMultiplicity v := by
  simp [State.sharedVertices]

theorem State.outside_private_disjoint (S : State V Flag) :
    Disjoint S.outsideVertices S.privateVertices := by
  rw [Finset.disjoint_left]
  intro v hvO hvP
  rw [S.mem_outsideVertices] at hvO
  rw [S.mem_privateVertices] at hvP
  omega

theorem State.outside_union_private_disjoint_shared (S : State V Flag) :
    Disjoint (S.outsideVertices ∪ S.privateVertices) S.sharedVertices := by
  rw [Finset.disjoint_left]
  intro v hvOP hvS
  rw [Finset.mem_union] at hvOP
  rw [S.mem_sharedVertices] at hvS
  rcases hvOP with hvO | hvP
  · rw [S.mem_outsideVertices] at hvO
    omega
  · rw [S.mem_privateVertices] at hvP
    omega

theorem State.outside_union_private_union_shared (S : State V Flag) :
    S.outsideVertices ∪ S.privateVertices ∪ S.sharedVertices = Finset.univ := by
  ext v
  simp only [Finset.mem_union, S.mem_outsideVertices,
    S.mem_privateVertices, S.mem_sharedVertices, Finset.mem_univ, iff_true]
  omega

/-- Exact cardinal partition of the live vertex type. -/
theorem State.card_live_partition (S : State V Flag) :
    Fintype.card V =
      S.outsideVertices.card + S.privateVertices.card + S.sharedVertices.card := by
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = (S.outsideVertices ∪ S.privateVertices ∪ S.sharedVertices).card := by
      rw [S.outside_union_private_union_shared]
    _ = S.outsideVertices.card + S.privateVertices.card +
          S.sharedVertices.card := by
      rw [Finset.card_union_of_disjoint
        S.outside_union_private_disjoint_shared,
        Finset.card_union_of_disjoint S.outside_private_disjoint]

/-! ## Exact completion-edge bookkeeping -/

omit [Fintype V] [Fintype Flag] in
private theorem ghostEdge_eq_iff
    {t u : Flag} {v w : V} :
    ghostEdge t v = ghostEdge u w ↔ t = u ∧ v = w := by
  constructor
  · intro h
    have ht : Sum.inr t ∈ (ghostEdge u w).vertices := by
      rw [← h]
      simp
    have hv : Sum.inl v ∈ (ghostEdge u w).vertices := by
      rw [← h]
      simp
    constructor
    · simpa using ht
    · simpa using hv
  · rintro ⟨rfl, rfl⟩
    rfl

omit [Fintype V] [Fintype Flag] in
private theorem ghostEdge_fixed_injective (t : Flag) :
    Function.Injective (ghostEdge t : V → SimpleEdge (V ⊕ Flag)) := by
  intro v w h
  exact (ghostEdge_eq_iff.mp h).2

private theorem ghostEdge_flags_disjoint
    (S : State V Flag) {t u : Flag} (htu : t ≠ u) :
    Disjoint
      ((S.terminals t).image fun v ↦ ghostEdge t v)
      ((S.terminals u).image fun v ↦ ghostEdge u v) := by
  rw [Finset.disjoint_left]
  intro e het heu
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp het
  obtain ⟨w, _hw, hwe⟩ := Finset.mem_image.mp heu
  have heq : ghostEdge t v = ghostEdge u w := hve.trans hwe.symm
  exact htu (ghostEdge_eq_iff.mp heq).1

private theorem pairwiseDisjoint_ghostStars (S : State V Flag) :
    ((Finset.univ : Finset Flag) : Set Flag).PairwiseDisjoint
      (fun t ↦ (S.terminals t).image fun v ↦ ghostEdge t v) := by
  intro t _ht u _hu htu
  exact ghostEdge_flags_disjoint S htu

@[simp]
theorem State.card_ghostStarEdges (S : State V Flag) :
    S.ghostStarEdges.card = 3 * Fintype.card Flag := by
  rw [State.ghostStarEdges,
    Finset.card_biUnion (pairwiseDisjoint_ghostStars S)]
  calc
    (∑ t ∈ (Finset.univ : Finset Flag),
        ((S.terminals t).image fun v ↦ ghostEdge t v).card) =
        ∑ _t ∈ (Finset.univ : Finset Flag), 3 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_image_of_injective _ (ghostEdge_fixed_injective t),
        S.terminals_card t]
    _ = 3 * Fintype.card Flag := by simp [Nat.mul_comm]

omit [Fintype V] [Fintype Flag] in
private theorem no_ghost_mem_liftLiveEdge_vertices
    (e : SimpleEdge V) (t : Flag) :
    Sum.inr t ∉ (liftLiveEdge (Flag := Flag) e).vertices := by
  intro ht
  obtain ⟨a, ha⟩ : e.vertices.Nonempty :=
    Finset.card_pos.mp (by simp)
  obtain ⟨b, hab, he⟩ := exists_otherEndpoint e ha
  rw [he] at ht
  simp [liftLiveEdge, simpleEdge, SimpleEdge.vertices,
    Sym2.toFinset_mk_eq] at ht

private theorem State.liftedLiveEdges_disjoint_ghostStarEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.ghostStarEdges := by
  rw [Finset.disjoint_left]
  intro e heLive heGhost
  obtain ⟨t, _ht, heStar⟩ := Finset.mem_biUnion.mp heGhost
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp heStar
  obtain ⟨f, _hf, hfe⟩ := Finset.mem_map.mp heLive
  have hghost : Sum.inr t ∈ e.vertices := by
    rw [← hve]
    simp
  rw [← hfe] at hghost
  exact no_ghost_mem_liftLiveEdge_vertices f t hghost

private theorem State.restoredMissingEdges_disjoint_ghostStarEdges
    (S : State V Flag) :
    Disjoint S.restoredMissingEdges S.ghostStarEdges := by
  rw [Finset.disjoint_left]
  intro e heMissing heGhost
  obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
  obtain ⟨u, _hu, heStar⟩ := Finset.mem_biUnion.mp heGhost
  obtain ⟨v, _hv, hve⟩ := Finset.mem_image.mp heStar
  have hghost : Sum.inr u ∈ e.vertices := by
    rw [← hve]
    simp
  rw [← hte] at hghost
  exact no_ghost_mem_liftLiveEdge_vertices (S.missing t) u hghost

private theorem State.liftedLiveEdges_disjoint_restoredMissingEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.restoredMissingEdges := by
  rw [Finset.disjoint_left]
  intro e heLive heMissing
  obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heMissing
  rw [← hte] at heLive
  exact S.missing_not_live t ((S.mem_liftedLiveEdges (S.missing t)).1 heLive)

private theorem State.missing_injective_of_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    Function.Injective S.missing := by
  intro t u htuEdge
  by_contra htu
  have hSupported : (S.missing t).vertices ⊆
      S.terminals t ∩ S.terminals u := by
    exact Finset.subset_inter (S.missing_supported t)
      (htuEdge ▸ S.missing_supported u)
  have hCard := Finset.card_le_card hSupported
  rw [(S.missing t).card_vertices] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

@[simp]
theorem State.card_restoredMissingEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.restoredMissingEdges.card = Fintype.card Flag := by
  rw [State.restoredMissingEdges,
    Finset.card_image_of_injective Finset.univ]
  · simp
  · intro t u htu
    apply S.missing_injective_of_completionSparse hSparse
    exact liftLiveEdge_injective htu

/-- Completion edges not already present in the live graph. -/
def State.extraCompletionEdges (S : State V Flag) :
    SimpleEdgeSet (V ⊕ Flag) :=
  S.restoredMissingEdges ∪ S.ghostStarEdges

@[simp]
theorem State.card_extraCompletionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.extraCompletionEdges.card = 4 * Fintype.card Flag := by
  rw [State.extraCompletionEdges,
    Finset.card_union_of_disjoint
      S.restoredMissingEdges_disjoint_ghostStarEdges,
    S.card_restoredMissingEdges hSparse, S.card_ghostStarEdges]
  omega

theorem State.liftedLiveEdges_disjoint_extraCompletionEdges
    (S : State V Flag) :
    Disjoint S.liftedLiveEdges S.extraCompletionEdges := by
  rw [State.extraCompletionEdges, Finset.disjoint_union_right]
  exact ⟨S.liftedLiveEdges_disjoint_restoredMissingEdges,
    S.liftedLiveEdges_disjoint_ghostStarEdges⟩

theorem State.completionEdges_eq_live_union_extra (S : State V Flag) :
    S.completionEdges = S.liftedLiveEdges ∪ S.extraCompletionEdges := by
  ext e
  simp [State.completionEdges, State.extraCompletionEdges]

/-- Exact completion ledger: each flag adds one restored terminal edge and
three private ghost edges. -/
@[simp]
theorem State.card_completionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse) :
    S.completionEdges.card = S.edges.card + 4 * Fintype.card Flag := by
  rw [S.completionEdges_eq_live_union_extra,
    Finset.card_union_of_disjoint
      S.liftedLiveEdges_disjoint_extraCompletionEdges,
    State.liftedLiveEdges, Finset.card_map,
    S.card_extraCompletionEdges hSparse]

/-- Full-universe consequence of completion sparsity, written without a
truncated subtraction. -/
theorem State.live_edge_budget
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (hV : (Finset.univ : Finset V).Nonempty) :
    S.edges.card + 2 * Fintype.card Flag + 2 ≤ 2 * Fintype.card V := by
  have hVCard : 1 ≤ Fintype.card V := by
    simpa using Finset.card_pos.mpr hV
  obtain ⟨v, _hv⟩ := hV
  have hUniverse : (Finset.univ : Finset (V ⊕ Flag)).Nonempty :=
    ⟨Sum.inl v, Finset.mem_univ _⟩
  have hBound := hSparse (Finset.univ : Finset (V ⊕ Flag)) hUniverse
  have hInside :
      edgesInside S.completionEdges (Finset.univ : Finset (V ⊕ Flag)) =
        S.completionEdges := by
    ext e
    simp
  rw [hInside, S.card_completionEdges hSparse] at hBound
  simp only [Finset.card_univ, Fintype.card_sum] at hBound
  omega

/-! ## Incidence and degree ledgers -/

/-- Live terminal edges of flag `t` incident with `v`. -/
def State.flagLiveEdgesAt (S : State V Flag) (t : Flag) (v : V) :
    SimpleEdgeSet V :=
  S.edges.filter fun e ↦ v ∈ e.vertices ∧ e.vertices ⊆ S.terminals t

@[simp]
theorem State.mem_flagLiveEdgesAt
    (S : State V Flag) (t : Flag) (v : V) (e : SimpleEdge V) :
    e ∈ S.flagLiveEdgesAt t v ↔
      e ∈ S.edges ∧ v ∈ e.vertices ∧ e.vertices ⊆ S.terminals t := by
  simp [State.flagLiveEdgesAt]

private theorem State.exists_flagLiveEdgeAt
    (S : State V Flag) (t : Flag) {v : V} (hv : v ∈ S.terminals t) :
    (S.flagLiveEdgesAt t v).Nonempty := by
  have hEraseCard : ((S.terminals t).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, S.terminals_card t]
  obtain ⟨a, b, hab, hErase⟩ := Finset.card_eq_two.mp hEraseCard
  have haErase : a ∈ (S.terminals t).erase v := by rw [hErase]; simp
  have hbErase : b ∈ (S.terminals t).erase v := by rw [hErase]; simp
  have hva : v ≠ a := (Finset.mem_erase.mp haErase).1.symm
  have hvb : v ≠ b := (Finset.mem_erase.mp hbErase).1.symm
  have ha : a ∈ S.terminals t := (Finset.mem_erase.mp haErase).2
  have hb : b ∈ S.terminals t := (Finset.mem_erase.mp hbErase).2
  let ea : SimpleEdge V := simpleEdge v a hva
  let eb : SimpleEdge V := simpleEdge v b hvb
  have heaSupported : ea.vertices ⊆ S.terminals t := by
    rw [show ea = simpleEdge v a hva from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact ha
  have hebSupported : eb.vertices ⊆ S.terminals t := by
    rw [show eb = simpleEdge v b hvb from rfl, vertices_simpleEdge]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hb
  have heab : ea ≠ eb := by
    intro heq
    rcases (simpleEdge_eq_simpleEdge_iff v a v b hva hvb).mp heq with
        ⟨_hvv, hab'⟩ | ⟨hvb', _hav⟩
    · exact hab hab'
    · exact hvb hvb'
  by_cases heaMissing : ea = S.missing t
  · have hebMissing : eb ≠ S.missing t := by
      intro heb
      exact heab (heaMissing.trans heb.symm)
    refine ⟨eb, S.mem_flagLiveEdgesAt t v eb |>.2 ⟨?_, ?_, hebSupported⟩⟩
    · exact S.other_terminal_edges_live t eb hebSupported hebMissing
    · rw [show eb = simpleEdge v b hvb from rfl, vertices_simpleEdge]
      simp
  · refine ⟨ea, S.mem_flagLiveEdgesAt t v ea |>.2 ⟨?_, ?_, heaSupported⟩⟩
    · exact S.other_terminal_edges_live t ea heaSupported heaMissing
    · rw [show ea = simpleEdge v a hva from rfl, vertices_simpleEdge]
      simp

private theorem State.disjoint_flagLiveEdgesAt
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V)
    {t u : Flag} (htu : t ≠ u) :
    Disjoint (S.flagLiveEdgesAt t v) (S.flagLiveEdgesAt u v) := by
  rw [Finset.disjoint_left]
  intro e het heu
  have hSubset : e.vertices ⊆ S.terminals t ∩ S.terminals u :=
    Finset.subset_inter (S.mem_flagLiveEdgesAt t v e |>.1 het).2.2
      (S.mem_flagLiveEdgesAt u v e |>.1 heu).2.2
  have hCard := Finset.card_le_card hSubset
  rw [e.card_vertices] at hCard
  have hOne := S.card_terminal_inter_le_one hSparse htu
  omega

private theorem State.pairwiseDisjoint_flagLiveEdgesAt
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V) :
    ((S.activeFlagsAt v : Finset Flag) : Set Flag).PairwiseDisjoint
      (fun t ↦ S.flagLiveEdgesAt t v) := by
  intro t _ht u _hu htu
  exact S.disjoint_flagLiveEdgesAt hSparse v htu

/-- Each flag incidence at `v` supplies a distinct incident live edge. -/
theorem State.flagMultiplicity_le_liveDegree
    (S : State V Flag) (hSparse : S.CompletionSparse) (v : V) :
    S.flagMultiplicity v ≤ edgeSetDegree S.edges v := by
  let U : SimpleEdgeSet V :=
    (S.activeFlagsAt v).biUnion fun t ↦ S.flagLiveEdgesAt t v
  have hEach :
      (∑ _t ∈ S.activeFlagsAt v, 1) ≤
        ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := by
    exact Finset.sum_le_sum fun t ht ↦
      Finset.card_pos.mpr
        (S.exists_flagLiveEdgeAt t ((S.mem_activeFlagsAt v t).1 ht))
  have hUnionCard :
      U.card = ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := by
    exact Finset.card_biUnion (S.pairwiseDisjoint_flagLiveEdgesAt hSparse v)
  have hUnionSubset : U ⊆ incidentEdges S.edges v := by
    intro e he
    obtain ⟨t, _ht, het⟩ := Finset.mem_biUnion.mp he
    have het' := (S.mem_flagLiveEdgesAt t v e).1 het
    exact mem_incidentEdges.mpr ⟨het'.1, het'.2.1⟩
  calc
    S.flagMultiplicity v = ∑ _t ∈ S.activeFlagsAt v, 1 := by
      simp [State.flagMultiplicity]
    _ ≤ ∑ t ∈ S.activeFlagsAt v, (S.flagLiveEdgesAt t v).card := hEach
    _ = U.card := hUnionCard.symm
    _ ≤ (incidentEdges S.edges v).card := Finset.card_le_card hUnionSubset
    _ = edgeSetDegree S.edges v := rfl

private theorem State.sum_flagMultiplicity_eq_sum_terminalCards
    (S : State V Flag) :
    (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
      ∑ t ∈ (Finset.univ : Finset Flag), (S.terminals t).card := by
  have hMultiplicity (v : V) :
      S.flagMultiplicity v =
        ∑ t ∈ (Finset.univ : Finset Flag),
          if v ∈ S.terminals t then 1 else 0 := by
    rw [State.flagMultiplicity, State.activeFlagsAt,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
        ∑ v ∈ (Finset.univ : Finset V),
          ∑ t ∈ (Finset.univ : Finset Flag),
            if v ∈ S.terminals t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hMultiplicity v
    _ = ∑ t ∈ (Finset.univ : Finset Flag),
          ∑ v ∈ (Finset.univ : Finset V),
            if v ∈ S.terminals t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ (Finset.univ : Finset Flag), (S.terminals t).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      calc
        (∑ v ∈ (Finset.univ : Finset V),
            if v ∈ S.terminals t then 1 else 0) =
            ((Finset.univ : Finset V).filter
              fun v ↦ v ∈ S.terminals t).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = (S.terminals t).card := by
          congr
          ext v
          simp

private theorem State.sum_over_live_partition
    (S : State V Flag) (f : V → ℕ) :
    (∑ v ∈ (Finset.univ : Finset V), f v) =
      (∑ v ∈ S.outsideVertices, f v) +
      (∑ v ∈ S.privateVertices, f v) +
      ∑ v ∈ S.sharedVertices, f v := by
  rw [← S.outside_union_private_union_shared,
    Finset.sum_union S.outside_union_private_disjoint_shared,
    Finset.sum_union S.outside_private_disjoint]

/-- Exact terminal-incidence ledger after splitting live vertices into the
private and shared classes. -/
theorem State.private_card_add_sharedIncidence
    (S : State V Flag) :
    S.privateVertices.card + S.sharedIncidence = 3 * Fintype.card Flag := by
  have hTotal := S.sum_flagMultiplicity_eq_sum_terminalCards
  have hTerminal := S.sum_card_terminals (Finset.univ : Finset Flag)
  have hSplit := S.sum_over_live_partition S.flagMultiplicity
  have hOutside :
      (∑ v ∈ S.outsideVertices, S.flagMultiplicity v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact (S.mem_outsideVertices v).1 hv
  have hPrivate :
      (∑ v ∈ S.privateVertices, S.flagMultiplicity v) =
        S.privateVertices.card := by
    calc
      (∑ v ∈ S.privateVertices, S.flagMultiplicity v) =
          ∑ _v ∈ S.privateVertices, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (S.mem_privateVertices v).1 hv
      _ = S.privateVertices.card := by simp
  rw [hOutside, hPrivate] at hSplit
  change (∑ v ∈ (Finset.univ : Finset V), S.flagMultiplicity v) =
      0 + S.privateVertices.card + S.sharedIncidence at hSplit
  rw [hTerminal] at hTotal
  simp only [Finset.card_univ] at hTotal
  omega

theorem State.two_mul_shared_card_le_sharedIncidence
    (S : State V Flag) :
    2 * S.sharedVertices.card ≤ S.sharedIncidence := by
  have hSum :
      (∑ _v ∈ S.sharedVertices, 2) ≤
        ∑ v ∈ S.sharedVertices, S.flagMultiplicity v := by
    exact Finset.sum_le_sum fun v hv ↦ (S.mem_sharedVertices v).1 hv
  simpa [State.sharedIncidence, Nat.mul_comm] using hSum

/-- The exact live-edge handshake on the full live vertex type. -/
theorem State.sum_liveDegree_eq_twice_edges (S : State V Flag) :
    (∑ v ∈ (Finset.univ : Finset V), edgeSetDegree S.edges v) =
      2 * S.edges.card := by
  apply sum_edgeSetDegree_eq_twice_card
  intro e _he v _hv
  exact Finset.mem_univ v

/-! ## The selection theorem -/

/-- Sparse completion forces a reducible live vertex: either a vertex
outside every flag has degree at most three, or a vertex private to one flag
has degree at most two. -/
theorem State.exists_outside_degree_le_three_or_private_degree_le_two
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (hV : (Finset.univ : Finset V).Nonempty) :
    (∃ v : V, S.flagMultiplicity v = 0 ∧ edgeSetDegree S.edges v ≤ 3) ∨
      ∃ v : V, S.flagMultiplicity v = 1 ∧ edgeSetDegree S.edges v ≤ 2 := by
  by_contra hSelection
  have hNoOutside :
      ∀ v : V, S.flagMultiplicity v = 0 → ¬ edgeSetDegree S.edges v ≤ 3 := by
    intro v hv hDegree
    exact hSelection (Or.inl ⟨v, hv, hDegree⟩)
  have hNoPrivate :
      ∀ v : V, S.flagMultiplicity v = 1 → ¬ edgeSetDegree S.edges v ≤ 2 := by
    intro v hv hDegree
    exact hSelection (Or.inr ⟨v, hv, hDegree⟩)
  have hOutsideDegree :
      ∀ v ∈ S.outsideVertices, 4 ≤ edgeSetDegree S.edges v := by
    intro v hv
    have hvZero := (S.mem_outsideVertices v).1 hv
    have hNot := hNoOutside v hvZero
    omega
  have hPrivateDegree :
      ∀ v ∈ S.privateVertices, 3 ≤ edgeSetDegree S.edges v := by
    intro v hv
    have hvOne := (S.mem_privateVertices v).1 hv
    have hNot := hNoPrivate v hvOne
    omega
  have hDegreeSplit := S.sum_over_live_partition (edgeSetDegree S.edges)
  have hOutsideLower :
      4 * S.outsideVertices.card ≤
        ∑ v ∈ S.outsideVertices, edgeSetDegree S.edges v := by
    have := Finset.sum_le_sum hOutsideDegree
    simpa [Nat.mul_comm] using this
  have hPrivateLower :
      3 * S.privateVertices.card ≤
        ∑ v ∈ S.privateVertices, edgeSetDegree S.edges v := by
    have := Finset.sum_le_sum hPrivateDegree
    simpa [Nat.mul_comm] using this
  have hSharedLower :
      S.sharedIncidence ≤
        ∑ v ∈ S.sharedVertices, edgeSetDegree S.edges v := by
    exact Finset.sum_le_sum fun v _hv ↦
      S.flagMultiplicity_le_liveDegree hSparse v
  have hDegreeLedger :
      4 * S.outsideVertices.card + 3 * S.privateVertices.card +
          S.sharedIncidence ≤ 2 * S.edges.card := by
    rw [← S.sum_liveDegree_eq_twice_edges, hDegreeSplit]
    omega
  exact not_all_flag_degrees_large
    (S.card_live_partition)
    (S.live_edge_budget hSparse hV)
    hDegreeLedger
    (S.private_card_add_sharedIncidence)
    (S.two_mul_shared_card_le_sharedIncidence)

end ProvenanceFlag

end

end RB31E2E
