import RB31EndToEnd.Combinatorics.Sparse22.OptimalPartition

/-!
# Same-vertex tight completion for `(2,2)`-sparse simple graphs

For at least four vertices, every `(2,2)`-sparse simple edge set extends,
without adding vertices, to a set tight on the full vertex universe.  The
proof maximizes among sparse supersets of the given set and derives the
augmentation property from tight-set uncrossing.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

private theorem two_mul_card_sub_one_le_choose_two {n : ℕ} (hn : 4 ≤ n) :
    2 * (n - 1) ≤ n.choose 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnsmall : n < 4
      · have hn3 : n = 3 := by omega
        subst n
        decide
      · have hrec := ih (by omega)
        have hchoose : n.succ.choose 2 = n + n.choose 2 := by
          simp only [Nat.choose_succ_succ, Nat.choose_one_right]
        rw [hchoose]
        omega

private theorem sym2_eq_of_toFinset_eq
    {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hvertices : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
          have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he
          have hcd : c ≠ d := by simpa [Sym2.mk_isDiag_iff] using hf
          have ha : a = c ∨ a = d := by
            have : a ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          have hb : b = c ∨ b = d := by
            have : b ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          rw [Sym2.eq_iff]
          rcases ha with hac | had <;> rcases hb with hbc | hbd
          · exact (hab (hac.trans hbc.symm)).elim
          · exact Or.inl ⟨hac, hbd⟩
          · exact Or.inr ⟨had, hbc⟩
          · exact (hab (had.trans hbd.symm)).elim

private theorem card_edgesInside_le_one_of_card_eq_two
    (F : SimpleEdgeSet V) {X : Finset V} (hX : X.card = 2) :
    (edgesInside F X).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  apply Subtype.ext
  apply sym2_eq_of_toFinset_eq e.2 f.2
  have heX := (mem_edgesInside.mp he).2
  have hfX := (mem_edgesInside.mp hf).2
  have heCard : e.vertices.card = X.card := by simp [hX]
  have hfCard : f.vertices.card = X.card := by simp [hX]
  have heEq : e.vertices = X :=
    Finset.eq_of_subset_of_card_le heX (by omega)
  have hfEq : f.vertices = X :=
    Finset.eq_of_subset_of_card_le hfX (by omega)
  exact heEq.trans hfEq.symm

private theorem tight22_card_ne_two
    {F : SimpleEdgeSet V} {X : Finset V} (hX : Tight22 F X) :
    X.card ≠ 2 := by
  intro hcard
  have hle := card_edgesInside_le_one_of_card_eq_two F hcard
  rw [hX.2, hcard] at hle
  omega

/-- A maximum-cardinality sparse superset of `F` inside `J`. -/
structure IsMaximumSparseSuperedge
    (F J G : SimpleEdgeSet V) : Prop where
  base_subset : F ⊆ G
  universe_subset : G ⊆ J
  sparse : Sparse22 G
  card_max : ∀ {K : SimpleEdgeSet V},
    F ⊆ K → K ⊆ J → Sparse22 K → K.card ≤ G.card

/-- Sparse supersets of `F` contained in `J`. -/
noncomputable def sparseSuperedges
    (F J : SimpleEdgeSet V) : Finset (SimpleEdgeSet V) := by
  classical
  exact J.powerset.filter fun G => F ⊆ G ∧ Sparse22 G

@[simp]
theorem mem_sparseSuperedges {F J G : SimpleEdgeSet V} :
    G ∈ sparseSuperedges F J ↔ G ⊆ J ∧ F ⊆ G ∧ Sparse22 G := by
  classical
  simp [sparseSuperedges]

theorem exists_isMaximumSparseSuperedge
    {F J : SimpleEdgeSet V} (hFJ : F ⊆ J) (hF : Sparse22 F) :
    ∃ G : SimpleEdgeSet V, IsMaximumSparseSuperedge F J G := by
  classical
  have hne : (sparseSuperedges F J).Nonempty := by
    refine ⟨F, ?_⟩
    exact mem_sparseSuperedges.mpr ⟨hFJ, Finset.Subset.rfl, hF⟩
  obtain ⟨G, hGmem, hGmax⟩ :=
    Finset.exists_max_image (sparseSuperedges F J) Finset.card hne
  have hG := mem_sparseSuperedges.mp hGmem
  refine ⟨G, hG.2.1, hG.1, hG.2.2, ?_⟩
  intro K hFK hKJ hKsparse
  exact hGmax K (mem_sparseSuperedges.mpr ⟨hKJ, hFK, hKsparse⟩)

theorem IsMaximumSparseSuperedge.not_sparse_insert
    {F J G : SimpleEdgeSet V} (hG : IsMaximumSparseSuperedge F J G)
    {e : SimpleEdge V} (heJ : e ∈ J) (heG : e ∉ G) :
    ¬ Sparse22 (insert e G) := by
  intro hins
  have hbase : F ⊆ insert e G := hG.base_subset.trans (Finset.subset_insert e G)
  have huniv : insert e G ⊆ J := Finset.insert_subset heJ hG.universe_subset
  have hcard := hG.card_max hbase huniv hins
  rw [Finset.card_insert_of_notMem heG] at hcard
  omega

/-- Every omitted complete-universe edge is internal to the tight partition. -/
theorem IsMaximumSparseSuperedge.internal_missing_edge
    [Fintype V]
    {F J G : SimpleEdgeSet V} (hG : IsMaximumSparseSuperedge F J G)
    {e : SimpleEdge V} (heJ : e ∈ J) (heG : e ∉ G) :
    InternalTo (tightPartition G hG.sparse) e := by
  obtain ⟨X, hXne, heX, hXtight⟩ :=
    exists_tight22_of_not_sparse22_insert hG.sparse heG
      (hG.not_sparse_insert heJ heG)
  obtain ⟨v, hvX⟩ := hXne
  refine ⟨(tightPartition G hG.sparse).part v, ?_, ?_⟩
  · exact (tightPartition G hG.sparse).part_mem.mpr (by simp)
  · rw [tightPartition_part_eq_tightHull]
    exact heX.trans (tight_subset_tightHull hXtight hvX)

/-- Edges induced by `A ∪ B` which are internal to neither side. -/
def betweenEdges (F : SimpleEdgeSet V) (A B : Finset V) : SimpleEdgeSet V :=
  edgesInside F (A ∪ B) \ (edgesInside F A ∪ edgesInside F B)

@[simp]
theorem mem_betweenEdges
    {F : SimpleEdgeSet V} {A B : Finset V} {e : SimpleEdge V} :
    e ∈ betweenEdges F A B ↔
      e ∈ F ∧ e.vertices ⊆ A ∪ B ∧
        ¬ e.vertices ⊆ A ∧ ¬ e.vertices ⊆ B := by
  simp only [betweenEdges, Finset.mem_sdiff, Finset.mem_union, mem_edgesInside]
  aesop

/-- Two disjoint tight sets can have at most two edges between them. -/
theorem card_betweenEdges_le_two_of_disjoint_tight
    {F : SimpleEdgeSet V} {A B : Finset V}
    (hF : Sparse22 F) (hA : Tight22 F A) (hB : Tight22 F B)
    (hAB : Disjoint A B) :
    (betweenEdges F A B).card ≤ 2 := by
  have hEdgeDisjoint : Disjoint (edgesInside F A) (edgesInside F B) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have hverts : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
    obtain ⟨v, hv⟩ := hverts
    exact (Finset.disjoint_left.mp hAB)
      ((mem_edgesInside.mp heA).2 hv) ((mem_edgesInside.mp heB).2 hv)
  have hInternalSubset :
      edgesInside F A ∪ edgesInside F B ⊆ edgesInside F (A ∪ B) :=
    union_edgesInside_subset F A B
  have hUnionNonempty : (A ∪ B).Nonempty :=
    hA.1.mono Finset.subset_union_left
  have hSparseUnion := hF (A ∪ B) hUnionNonempty
  have hVertexCard : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hAB
  rw [hVertexCard] at hSparseUnion
  unfold betweenEdges
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hInternalSubset,
    Finset.card_union_of_disjoint hEdgeDisjoint, hA.2, hB.2]
  have hApos : 0 < A.card := Finset.card_pos.mpr hA.1
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB.1
  omega

/-- Join every vertex of `A` to one vertex outside `A`. -/
def starEdgeEmbedding (A : Finset V) (b : V) (hb : b ∉ A) :
    {a // a ∈ A} ↪ SimpleEdge V where
  toFun a := ⟨s(a.1, b), by
    rw [Sym2.mk_isDiag_iff]
    intro hab
    exact hb (hab ▸ a.2)⟩
  inj' := by
    intro a c hac
    apply Subtype.ext
    have hp : s(a.1, b) = s(c.1, b) := congr_arg Subtype.val hac
    rw [Sym2.eq_iff] at hp
    rcases hp with hp | hp
    · exact hp.1
    · exact (hb (hp.1 ▸ a.2)).elim

/-- The simple star from `A` to an outside vertex `b`. -/
noncomputable def starEdges (A : Finset V) (b : V) (hb : b ∉ A) :
    SimpleEdgeSet V := by
  classical
  exact Finset.univ.map (starEdgeEmbedding A b hb)

omit [DecidableEq V] in
@[simp]
theorem card_starEdges (A : Finset V) (b : V) (hb : b ∉ A) :
    (starEdges A b hb).card = A.card := by
  classical
  simp [starEdges]

omit [DecidableEq V] in
@[simp]
theorem mem_starEdges_iff (A : Finset V) (b : V) (hb : b ∉ A)
    (e : SimpleEdge V) :
    e ∈ starEdges A b hb ↔
      ∃ a : V, a ∈ A ∧ e.1 = s(a, b) := by
  classical
  simp only [starEdges, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact he.symm

private def completeEdgeEquivForTightCompletion [Fintype V] :
    (⊤ : SimpleGraph V).edgeFinset ≃ SimpleEdge V where
  toFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using e.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

private theorem card_univ_simpleEdges [Fintype V] :
    (Finset.univ : SimpleEdgeSet V).card = (Fintype.card V).choose 2 := by
  rw [Finset.card_univ]
  calc
    Fintype.card (SimpleEdge V) =
        Fintype.card (⊤ : SimpleGraph V).edgeFinset :=
      Fintype.card_congr completeEdgeEquivForTightCompletion.symm
    _ = (⊤ : SimpleGraph V).edgeFinset.card :=
      Fintype.card_coe (⊤ : SimpleGraph V).edgeFinset
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

private theorem IsMaximumSparseSuperedge.starEdges_subset_betweenEdges
    [Fintype V]
    {F G : SimpleEdgeSet V}
    (hG : IsMaximumSparseSuperedge F (Finset.univ : SimpleEdgeSet V) G)
    (A B : (tightPartition G hG.sparse).parts) (hAB : A ≠ B)
    (b : V) (hbB : b ∈ B.1) (hbA : b ∉ A.1) :
    starEdges A.1 b hbA ⊆ betweenEdges G A.1 B.1 := by
  intro e heStar
  obtain ⟨a, haA, heval⟩ := (mem_starEdges_iff A.1 b hbA e).mp heStar
  let ea : SimpleEdge V := starEdgeEmbedding A.1 b hbA ⟨a, haA⟩
  have heq : e = ea := by
    apply Subtype.ext
    exact heval
  subst e
  have hab : a ≠ b := by
    intro hab
    exact hbA (hab ▸ haA)
  have haNotB : a ∉ B.1 := by
    have hABval : A.1 ≠ B.1 := fun h => hAB (Subtype.ext h)
    exact (Finset.disjoint_left.mp
      ((tightPartition G hG.sparse).disjoint A.2 B.2 hABval)) haA
  have hnotInternal : ¬ InternalTo (tightPartition G hG.sparse) ea := by
    rintro ⟨X, hX, heX⟩
    have haX : a ∈ X := heX (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq])
    have hbX : b ∈ X := heX (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq])
    have hAX : A.1 = X := by
      exact ((tightPartition G hG.sparse).part_eq_of_mem A.2 haA).symm.trans
        ((tightPartition G hG.sparse).part_eq_of_mem hX haX)
    have hBX : B.1 = X := by
      exact ((tightPartition G hG.sparse).part_eq_of_mem B.2 hbB).symm.trans
        ((tightPartition G hG.sparse).part_eq_of_mem hX hbX)
    apply hAB
    apply Subtype.ext
    exact hAX.trans hBX.symm
  have heaG : ea ∈ G := by
    by_contra heaG
    exact hnotInternal (hG.internal_missing_edge (by simp) heaG)
  rw [mem_betweenEdges]
  refine ⟨heaG, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v = a ∨ v = b := by
      have : v ∈ ea.1 := Sym2.mem_toFinset.mp hv
      simpa [ea, starEdgeEmbedding] using this
    rcases hv' with hva | hvb
    · subst v
      exact Finset.mem_union_left _ haA
    · subst v
      exact Finset.mem_union_right _ hbB
  · intro hsub
    exact hbA (hsub (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq]))
  · intro hsub
    exact haNotB (hsub (by
      simp [ea, starEdgeEmbedding, SimpleEdge.vertices, Sym2.toFinset_mk_eq]))

/--
Every `(2,2)`-sparse simple edge set on at least four vertices has a
same-vertex `(2,2)`-tight completion.
-/
theorem exists_tight22_completion
    [Fintype V]
    (F : SimpleEdgeSet V) (hF : Sparse22 F) (hcard : 4 ≤ Fintype.card V) :
    ∃ G : SimpleEdgeSet V,
      F ⊆ G ∧ Sparse22 G ∧ Tight22 G (Finset.univ : Finset V) := by
  classical
  let J : SimpleEdgeSet V := Finset.univ
  obtain ⟨G, hG⟩ := exists_isMaximumSparseSuperedge
    (F := F) (J := J) (by simp [J]) hF
  refine ⟨G, hG.base_subset, hG.sparse, ?_⟩
  have hUnivNonempty : (Finset.univ : Finset V).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_univ]
    omega
  refine ⟨hUnivNonempty, ?_⟩
  by_contra hnotTight
  have hGupper := hG.sparse (Finset.univ : Finset V) hUnivNonempty
  have hGstrict : G.card < 2 * (Fintype.card V - 1) := by
    have hInside : edgesInside G (Finset.univ : Finset V) = G := by
      ext e
      simp [edgesInside]
    rw [hInside, Finset.card_univ] at hGupper hnotTight
    omega
  let P := tightPartition G hG.sparse
  have hpartsTwo : 2 ≤ P.parts.card := by
    by_contra hnotTwo
    have hpartsNonempty : P.parts.Nonempty := by
      obtain ⟨v, hv⟩ := hUnivNonempty
      exact ⟨P.part v, P.part_mem.mpr (by simp)⟩
    have hpartsCard : P.parts.card = 1 := by
      have hpos := Finset.card_pos.mpr hpartsNonempty
      omega
    obtain ⟨X, hpartsEq⟩ := Finset.card_eq_one.mp hpartsCard
    have hXmem : X ∈ P.parts := by simp [hpartsEq]
    have hXuniv : X = (Finset.univ : Finset V) := by
      apply Finset.eq_univ_of_forall
      intro v
      have hvpart : P.part v ∈ P.parts := P.part_mem.mpr (by simp)
      have hvpartEq : P.part v = X := by
        rw [hpartsEq] at hvpart
        simpa using hvpart
      rw [← hvpartEq]
      exact P.mem_part (by simp)
    have hXtight : Tight22 G X := by
      exact tight_of_mem_tightPartition hG.sparse hXmem
    rw [hXuniv] at hXtight
    exact hnotTight hXtight.2
  by_cases hlarge : ∃ A : P.parts, 1 < A.1.card
  · obtain ⟨A, hAcardTwo⟩ := hlarge
    have hAtight : Tight22 G A.1 := by
      exact tight_of_mem_tightPartition hG.sparse A.2
    have hAcardThree : 3 ≤ A.1.card := by
      have hAneTwo := tight22_card_ne_two hAtight
      omega
    obtain ⟨B0, hB0mem, hB0ne⟩ :=
      Finset.exists_mem_ne (by omega : 1 < P.parts.card) A.1
    let B : P.parts := ⟨B0, hB0mem⟩
    have hAB : A ≠ B := by
      intro hEq
      exact hB0ne (congr_arg Subtype.val hEq).symm
    have hABval : A.1 ≠ B.1 := fun hEq => hAB (Subtype.ext hEq)
    have hABdisjoint : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hABval
    obtain ⟨b, hbB⟩ := P.nonempty_of_mem_parts B.2
    have hbA : b ∉ A.1 := by
      intro hbA
      exact (Finset.disjoint_left.mp hABdisjoint) hbA hbB
    have hstarSubset :
        starEdges A.1 b hbA ⊆ betweenEdges G A.1 B.1 := by
      exact hG.starEdges_subset_betweenEdges A B hAB b hbB hbA
    have hstarCard : A.1.card ≤ (betweenEdges G A.1 B.1).card := by
      rw [← card_starEdges A.1 b hbA]
      exact Finset.card_le_card hstarSubset
    have hBtight : Tight22 G B.1 := by
      exact tight_of_mem_tightPartition hG.sparse B.2
    have hbetween := card_betweenEdges_le_two_of_disjoint_tight
      hG.sparse hAtight hBtight hABdisjoint
    omega
  · have hcompleteBudget :
        2 * (Fintype.card V - 1) ≤
          (Finset.univ : SimpleEdgeSet V).card := by
      rw [card_univ_simpleEdges]
      exact two_mul_card_sub_one_le_choose_two hcard
    have hGcardLt : G.card < (Finset.univ : SimpleEdgeSet V).card :=
      hGstrict.trans_le hcompleteBudget
    have hGne : G ≠ (Finset.univ : SimpleEdgeSet V) := by
      intro hEq
      rw [hEq] at hGcardLt
      omega
    have hGproper : G ⊂ (Finset.univ : SimpleEdgeSet V) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨by simp, hGne⟩
    obtain ⟨e, heUniv, heG⟩ := Finset.exists_of_ssubset hGproper
    have heInternal : InternalTo P e := by
      exact hG.internal_missing_edge (by simp [J]) heG
    obtain ⟨X, hXmem, heX⟩ := heInternal
    have hXcard : X.card ≤ 1 := by
      have hnotLarge : ¬ 1 < X.card := by
        intro hXlarge
        apply hlarge
        exact ⟨⟨X, hXmem⟩, hXlarge⟩
      omega
    have hvertices := Finset.card_le_card heX
    rw [e.card_vertices] at hvertices
    omega

end RB31E2E
