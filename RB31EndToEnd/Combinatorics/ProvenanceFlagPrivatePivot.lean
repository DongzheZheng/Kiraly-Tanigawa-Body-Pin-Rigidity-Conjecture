import RB31EndToEnd.Combinatorics.ProvenanceFlagPrivateMove

/-!
# Pivoting the distinguished missing edge of a private flag

If the old missing terminal edge is opposite a private terminal `v`, this
file exchanges it with one incident live terminal edge.  The live edge set
and restored-missing packet swap one edge each, so the literal provenance
completion is unchanged.  No semismallness or stress assertion is stored
in the resulting state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Exchange the opposite missing edge `pq` with the incident edge `vq`.
The hypotheses describe only facts derivable from the old literal state. -/
def State.pivotPrivateOpposite
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    State V Flag where
  edges := insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
  terminals := S.terminals
  missing u := if h : u = t then simpleEdge v q hvq else S.missing u
  terminals_card := S.terminals_card
  missing_supported u := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)]
      rw [vertices_simpleEdge, hTerminals]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · rw [dif_neg hut]
      exact S.missing_supported u
  missing_not_live u := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)]
      change simpleEdge v q hvq ∉
        insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
      intro hmem
      rcases Finset.mem_insert.mp hmem with hEq | hErase
      · rw [simpleEdge_eq_simpleEdge_iff] at hEq
        rcases hEq with h | h
        · exact hvp h.1
        · exact hvq h.1
      · exact (Finset.mem_erase.mp hErase).1 rfl
    · rw [dif_neg hut]
      change S.missing u ∉
        insert (simpleEdge p q hpq) (S.edges.erase (simpleEdge v q hvq))
      intro hmem
      rcases Finset.mem_insert.mp hmem with hEq | hErase
      · have hpU : p ∈ S.terminals u := by
          apply S.missing_supported u
          rw [hEq, vertices_simpleEdge]
          simp
        have hqU : q ∈ S.terminals u := by
          apply S.missing_supported u
          rw [hEq, vertices_simpleEdge]
          simp
        have hpT : p ∈ S.terminals t := by rw [hTerminals]; simp
        have hqT : q ∈ S.terminals t := by rw [hTerminals]; simp
        have hTwo : 2 ≤ (S.terminals t ∩ S.terminals u).card := by
          have hPair : ({p, q} : Finset V) ⊆
              S.terminals t ∩ S.terminals u := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hpT, hpU⟩
            · exact Finset.mem_inter.mpr ⟨hqT, hqU⟩
          have hCardPair : ({p, q} : Finset V).card = 2 := by simp [hpq]
          rw [← hCardPair]
          exact Finset.card_le_card hPair
        have hAtMost := S.card_terminal_inter_le_one hSparse (Ne.symm hut)
        omega
      · exact S.missing_not_live u (Finset.mem_erase.mp hErase).2
  other_terminal_edges_live u e heT heMissingNew := by
    by_cases hut : u = t
    · subst u
      rw [dif_pos (by rfl)] at heMissingNew
      change e ≠ simpleEdge v q hvq at heMissingNew
      by_cases heOldMissing : e = simpleEdge p q hpq
      · subst e
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_, S.other_terminal_edges_live t e heT ?_⟩
        · exact heMissingNew
        · intro hEq
          exact heOldMissing (hEq.trans hMissing)
    · rw [dif_neg hut] at heMissingNew
      change e ≠ S.missing u at heMissingNew
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨?_, S.other_terminal_edges_live u e heT heMissingNew⟩
      intro heq
      subst e
      have hvU : v ∈ S.terminals u := by
        apply heT
        rw [vertices_simpleEdge]
        simp
      exact (not_mem_other_terminals_of_flagMultiplicity_eq_one
        S v t hOne hvt u hut hvU)

@[simp]
theorem State.pivotPrivateOpposite_edges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).edges =
      insert (simpleEdge p q hpq)
        (S.edges.erase (simpleEdge v q hvq)) := rfl

@[simp]
theorem State.pivotPrivateOpposite_terminals
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t u : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).terminals u = S.terminals u := rfl

@[simp]
theorem State.pivotPrivateOpposite_missing_self
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).missing t =
      simpleEdge v q hvq := by
  simp [State.pivotPrivateOpposite]

@[simp]
theorem State.pivotPrivateOpposite_missing_other
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t u : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq)
    (hut : u ≠ t) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).missing u = S.missing u := by
  simp [State.pivotPrivateOpposite, hut]

/-- The edge swapped into the live graph is exactly the old restored edge,
and the edge swapped out becomes exactly the new restored edge; therefore
the full completion is literally unchanged. -/
theorem State.pivotPrivateOpposite_completionEdges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).completionEdges =
      S.completionEdges := by
  let S' := S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
    hOne hvt hTerminals hMissing
  have hMissingSelf : S'.missing t = simpleEdge v q hvq := by
    simpa only [S'] using S.pivotPrivateOpposite_missing_self hSparse
      v p q t hvp hvq hpq hOne hvt hTerminals hMissing
  have hMissingOther (u : Flag) (hut : u ≠ t) :
      S'.missing u = S.missing u := by
    simpa only [S'] using S.pivotPrivateOpposite_missing_other hSparse
      v p q t u hvp hvq hpq hOne hvt hTerminals hMissing hut
  ext e
  rw [State.completionEdges, State.completionEdges]
  simp only [Finset.mem_union]
  constructor
  · rintro ((heLive | heMissing) | heGhost)
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
      change f ∈ insert (simpleEdge p q hpq)
        (S.edges.erase (simpleEdge v q hvq)) at hf
      rcases Finset.mem_insert.mp hf with rfl | hfOld
      · left; right
        exact Finset.mem_image.mpr
          ⟨t, Finset.mem_univ t, by
            change liftLiveEdge (Flag := Flag) (S.missing t) =
              liftLiveEdge (Flag := Flag) (simpleEdge p q hpq)
            rw [hMissing]⟩
      · left; left
        exact Finset.mem_map.mpr
          ⟨f, (Finset.mem_erase.mp hfOld).2, rfl⟩
    · obtain ⟨u, _hu, heu⟩ := Finset.mem_image.mp heMissing
      by_cases hut : u = t
      · subst u
        rw [hMissingSelf] at heu
        rw [← heu]
        left; left
        exact Finset.mem_map.mpr
          ⟨simpleEdge v q hvq,
            S.other_terminal_edges_live t _ (by
              rw [vertices_simpleEdge, hTerminals]
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inr rfl)) (by
              intro hEq
              rw [hMissing, simpleEdge_eq_simpleEdge_iff] at hEq
              rcases hEq with h | h
              · exact hvp h.1
              · exact hvq h.1), rfl⟩
      · left; right
        rw [hMissingOther u hut] at heu
        exact Finset.mem_image.mpr
          ⟨u, Finset.mem_univ u, by
            change liftLiveEdge (Flag := Flag) (S.missing u) = e
            exact heu⟩
    · right
      exact heGhost
  · rintro ((heLive | heMissing) | heGhost)
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp heLive
      by_cases hfq : f = simpleEdge v q hvq
      · subst f
        left; right
        exact Finset.mem_image.mpr
          ⟨t, Finset.mem_univ t, by
            change liftLiveEdge (Flag := Flag) (S'.missing t) =
              liftLiveEdge (Flag := Flag) (simpleEdge v q hvq)
            rw [hMissingSelf]⟩
      · left; left
        exact Finset.mem_map.mpr
          ⟨f, by
            change f ∈ insert (simpleEdge p q hpq)
              (S.edges.erase (simpleEdge v q hvq))
            exact Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hfq, hf⟩), rfl⟩
    · obtain ⟨u, _hu, heu⟩ := Finset.mem_image.mp heMissing
      by_cases hut : u = t
      · subst u
        rw [hMissing] at heu
        left; left
        exact Finset.mem_map.mpr
          ⟨simpleEdge p q hpq, by
            change simpleEdge p q hpq ∈ insert (simpleEdge p q hpq)
              (S.edges.erase (simpleEdge v q hvq))
            exact Finset.mem_insert_self _ _, heu⟩
      · left; right
        exact Finset.mem_image.mpr
          ⟨u, Finset.mem_univ u, by
            change liftLiveEdge (Flag := Flag) (S'.missing u) = e
            rw [hMissingOther u hut]
            exact heu⟩
    · right
      exact heGhost

/-- Completion sparsity is preserved because the completed edge set is
unchanged, not merely because it embeds in the old one. -/
theorem State.pivotPrivateOpposite_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).CompletionSparse := by
  rw [State.CompletionSparse,
    S.pivotPrivateOpposite_completionEdges hSparse v p q t
      hvp hvq hpq hOne hvt hTerminals hMissing]
  exact hSparse

/-- The pivot does not increase the selected private terminal's live
degree; the newly inserted opposite edge avoids `v`. -/
theorem State.pivotPrivateOpposite_degree_le
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    edgeSetDegree
        (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
          hOne hvt hTerminals hMissing).edges v ≤
      edgeSetDegree S.edges v := by
  apply Finset.card_le_card
  intro e he
  have heData := mem_incidentEdges.mp he
  rw [S.pivotPrivateOpposite_edges] at heData
  rcases Finset.mem_insert.mp heData.1 with hEq | heOld
  · subst e
    rw [vertices_simpleEdge] at heData
    simp [hvp, hvq] at heData
  · exact mem_incidentEdges.mpr ⟨(Finset.mem_erase.mp heOld).2, heData.2⟩

@[simp]
theorem State.pivotPrivateOpposite_flagMultiplicity
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t)
    (hTerminals : S.terminals t = {v, p, q})
    (hMissing : S.missing t = simpleEdge p q hpq) :
    (S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
      hOne hvt hTerminals hMissing).flagMultiplicity v =
      S.flagMultiplicity v := rfl

/-! ## Extracting an oriented pivot from an arbitrary private flag -/

omit [Fintype V] in
/-- A simple edge supported on a named three-element terminal set is one
of its three unordered pairs. -/
theorem simpleEdge_eq_one_of_three_of_supported
    (e : SimpleEdge V) (v a b : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hSupported : e.vertices ⊆ ({v, a, b} : Finset V)) :
    e = simpleEdge v a hva ∨ e = simpleEdge v b hvb ∨
      e = simpleEdge a b hab := by
  obtain ⟨x, hx⟩ : e.vertices.Nonempty :=
    Finset.card_pos.mp (by simp)
  obtain ⟨y, hxy, heq⟩ := exists_otherEndpoint e hx
  have hxCases : x = v ∨ x = a ∨ x = b := by
    have hxT := hSupported hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxT
  have hyMem : y ∈ e.vertices := by
    rw [heq, vertices_simpleEdge]
    simp
  have hyCases : y = v ∨ y = a ∨ y = b := by
    have hyT := hSupported hyMem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hyT
  rcases hxCases with rfl | rfl | rfl <;>
    rcases hyCases with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · left
    simpa using heq
  · right; left
    simpa using heq
  · left
    rw [simpleEdge_comm]
    simpa using heq
  · exact (hxy rfl).elim
  · right; right
    simpa using heq
  · right; left
    rw [simpleEdge_comm]
    simpa using heq
  · right; right
    rw [simpleEdge_comm]
    simpa using heq
  · exact (hxy rfl).elim

/-- Canonical data for the private-local classifier: `p` is a live
terminal neighbour of `v`, `q` is the other terminal, and `vq` is the
distinguished missing edge.  The state may be the original state or the
literal completion-preserving opposite-edge pivot. -/
structure PrivatePivotData
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) where
  state : State V Flag
  p : V
  q : V
  hvp : v ≠ p
  hvq : v ≠ q
  hpq : p ≠ q
  original_terminals : S.terminals t = {v, p, q}
  terminals : state.terminals t = {v, p, q}
  multiplicity : state.flagMultiplicity v = 1
  mem_terminal : v ∈ state.terminals t
  completionSparse : state.CompletionSparse
  completionEdges_eq : state.completionEdges = S.completionEdges
  vp_live : simpleEdge v p hvp ∈ state.edges
  pq_live : simpleEdge p q hpq ∈ state.edges
  vq_missing : state.missing t = simpleEdge v q hvq
  degree_le : edgeSetDegree state.edges v ≤ edgeSetDegree S.edges v
  pivoted : state = S ∨
    ∃ (_hVQLive : simpleEdge v q hvq ∈ S.edges)
      (hPQMissing : S.missing t = simpleEdge p q hpq),
      state = S.pivotPrivateOpposite hSparse v p q t hvp hvq hpq
        hOne hvt original_terminals hPQMissing

@[simp]
theorem PrivatePivotData.terminals_eq
    {S : State V Flag} {hSparse : S.CompletionSparse}
    {v : V} {t : Flag}
    {hOne : S.flagMultiplicity v = 1} {hvt : v ∈ S.terminals t}
    (D : PrivatePivotData S hSparse v t hOne hvt) (u : Flag) :
    D.state.terminals u = S.terminals u := by
  rcases D.pivoted with hState | ⟨_hVQLive, hPQMissing, hState⟩
  · rw [hState]
  · rw [hState]
    rfl

/-- Every private terminal admits an orientation in which the distinguished
missing edge meets `v`.  If the old
missing edge is already incident to `v`, this only renames endpoints; if it
is opposite `v`, the returned state is `pivotPrivateOpposite`. -/
theorem State.exists_privatePivotData
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (t : Flag)
    (hOne : S.flagMultiplicity v = 1) (hvt : v ∈ S.terminals t) :
    Nonempty (PrivatePivotData S hSparse v t hOne hvt) := by
  have solve (a b : V)
      (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
      (hTermAB : S.terminals t = {v, a, b}) :
      Nonempty (PrivatePivotData S hSparse v t hOne hvt) := by
    have hMissingCases := simpleEdge_eq_one_of_three_of_supported
      (S.missing t) v a b hva hvb hab (by
        rw [← hTermAB]
        exact S.missing_supported t)
    rcases hMissingCases with hvaMissing | hvbMissing | habMissing
    · refine ⟨{
        state := S, p := b, q := a,
        hvp := hvb, hvq := hva, hpq := hab.symm,
        original_terminals := by
          rw [hTermAB]
          ext u
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto,
        terminals := by
          rw [hTermAB]
          ext u
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto,
        multiplicity := hOne, mem_terminal := hvt,
        completionSparse := hSparse, completionEdges_eq := rfl,
        vp_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)) (by
          rw [hvaMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hab h.2.symm
          · exact hva h.1),
        pq_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)) (by
          rw [hvaMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hvb h.1.symm
          · exact hab h.1.symm),
        vq_missing := hvaMissing,
        degree_le := le_rfl,
        pivoted := Or.inl rfl }⟩
    · refine ⟨{
        state := S, p := a, q := b,
        hvp := hva, hvq := hvb, hpq := hab,
        original_terminals := hTermAB,
        terminals := hTermAB,
        multiplicity := hOne, mem_terminal := hvt,
        completionSparse := hSparse, completionEdges_eq := rfl,
        vp_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)) (by
          rw [hvbMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hab h.2
          · exact hvb h.1),
        pq_live := S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)) (by
          rw [hvbMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1.symm
          · exact hab h.1),
        vq_missing := hvbMissing,
        degree_le := le_rfl,
        pivoted := Or.inl rfl }⟩
    · let S' := S.pivotPrivateOpposite hSparse v a b t
        hva hvb hab hOne hvt hTermAB habMissing
      have hvaLive : simpleEdge v a hva ∈ S.edges :=
        S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)) (by
          rw [habMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1
          · exact hvb h.1)
      have hvbLive : simpleEdge v b hvb ∈ S.edges :=
        S.other_terminal_edges_live t _ (by
          rw [vertices_simpleEdge, hTermAB]
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)) (by
          rw [habMissing]
          intro hEq
          rw [simpleEdge_eq_simpleEdge_iff] at hEq
          rcases hEq with h | h
          · exact hva h.1
          · exact hvb h.1)
      refine ⟨{
        state := S', p := a, q := b,
        hvp := hva, hvq := hvb, hpq := hab,
        original_terminals := hTermAB,
        terminals := by simpa [S'] using hTermAB,
        multiplicity := by simpa [S'] using hOne,
        mem_terminal := by simpa [S'] using hvt,
        completionSparse := S.pivotPrivateOpposite_completionSparse
          hSparse v a b t hva hvb hab hOne hvt hTermAB habMissing,
        completionEdges_eq := S.pivotPrivateOpposite_completionEdges
          hSparse v a b t hva hvb hab hOne hvt hTermAB habMissing,
        vp_live := by
          change simpleEdge v a hva ∈ insert (simpleEdge a b hab)
            (S.edges.erase (simpleEdge v b hvb))
          exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by
              intro hEq
              rw [simpleEdge_eq_simpleEdge_iff] at hEq
              rcases hEq with h | h
              · exact hab h.2
              · exact hvb h.1,
              hvaLive⟩),
        pq_live := by
          change simpleEdge a b hab ∈ insert (simpleEdge a b hab)
            (S.edges.erase (simpleEdge v b hvb))
          exact Finset.mem_insert_self _ _,
        vq_missing :=
          S.pivotPrivateOpposite_missing_self hSparse v a b t
            hva hvb hab hOne hvt hTermAB habMissing,
        degree_le := S.pivotPrivateOpposite_degree_le hSparse v a b t
          hva hvb hab hOne hvt hTermAB habMissing,
        pivoted := Or.inr ⟨hvbLive, habMissing, rfl⟩ }⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, hTerm⟩ :=
    Finset.card_eq_three.mp (S.terminals_card t)
  have hvCases : v = x ∨ v = y ∨ v = z := by
    rw [hTerm] at hvt
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvt
  rcases hvCases with rfl | rfl | rfl
  · exact solve y z hxy hxz hyz hTerm
  · apply solve x z hxy.symm hyz hxz
    rw [hTerm]
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · apply solve x y hxz.symm hyz.symm hxy
    rw [hTerm]
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

end ProvenanceFlag

end

end RB31E2E
