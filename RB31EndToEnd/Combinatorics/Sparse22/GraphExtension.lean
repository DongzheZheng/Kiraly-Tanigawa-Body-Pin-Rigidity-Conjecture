import RB31EndToEnd.Combinatorics.Sparse22.TriangleSequence

/-!
# Proper tight modules and graph-extension reduction

This file develops the shorter replacement for the long triangle-sequence
branch in the simple `(2,2)`-tight construction theorem.  Starting from a
proper tight seed (in the intended application, the named `K₄` around a
degree-three vertex), we choose a maximum-cardinality proper tight
superset.  Tightness alone then forces every outside vertex to send at most
one edge into the module, unless that vertex already has degree two and
supplies an inverse Henneberg-one reduction.

The formulation keeps the exact source edge sets.  In particular,
`newEdgesAt` is not a numerical proxy: its elements are precisely the
source edges acquired when one outside vertex is adjoined to the module.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- The six provenance edges of a named `K₄` make its four-vertex set
`(2,2)`-tight.  This is the seed used by the graph-extension branch. -/
theorem tight22_namedK4Vertices
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F) (hK : NamedK4Witness F v a b c) :
    Tight22 F (namedK4Vertices v a b c) := by
  let K : Finset V := namedK4Vertices v a b c
  let E : SimpleEdgeSet V :=
    { simpleEdge v a hK.hva,
      simpleEdge v b hK.hvb,
      simpleEdge v c hK.hvc,
      simpleEdge a b hK.hab,
      simpleEdge a c hK.hac,
      simpleEdge b c hK.hbc }
  have he₁ : simpleEdge v a hK.hva ∉
      ({ simpleEdge v b hK.hvb, simpleEdge v c hK.hvc,
        simpleEdge a b hK.hab, simpleEdge a c hK.hac,
        simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc,
      hK.hab, hK.hac]
  have he₂ : simpleEdge v b hK.hvb ∉
      ({ simpleEdge v c hK.hvc, simpleEdge a b hK.hab,
        simpleEdge a c hK.hac, simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc, hK.hbc]
  have he₃ : simpleEdge v c hK.hvc ∉
      ({ simpleEdge a b hK.hab, simpleEdge a c hK.hac,
        simpleEdge b c hK.hbc } : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hva, hK.hvb, hK.hvc]
  have he₄ : simpleEdge a b hK.hab ∉
      ({simpleEdge a c hK.hac, simpleEdge b c hK.hbc} : SimpleEdgeSet V) := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hab, hK.hac, hK.hbc]
  have he₅ : simpleEdge a c hK.hac ≠ simpleEdge b c hK.hbc := by
    simp [simpleEdge_eq_simpleEdge_iff, hK.hab, hK.hac]
  have hEcard : E.card = 6 := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem he₁,
      Finset.card_insert_of_notMem he₂,
      Finset.card_insert_of_notMem he₃,
      Finset.card_insert_of_notMem he₄]
    simp [he₅]
  have pair_subset_K {x y : V} (hx : x ∈ K) (hy : y ∈ K) :
      ({x, y} : Finset V) ⊆ K := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hx
    · exact hy
  have hEsub : E ⊆ edgesInside F K := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · apply mem_edgesInside.mpr
      refine ⟨hK.va_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.vb_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.vc_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.ab_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.ac_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
    · apply mem_edgesInside.mpr
      refine ⟨hK.bc_mem, ?_⟩
      rw [vertices_simpleEdge]
      exact pair_subset_K (by simp [K, namedK4Vertices])
        (by simp [K, namedK4Vertices])
  have hLower : 6 ≤ (edgesInside F K).card := by
    rw [← hEcard]
    exact Finset.card_le_card hEsub
  have hKcard : K.card = 4 := card_namedK4Vertices hK
  have hUpper := hSparse K ⟨v, by simp [K, namedK4Vertices]⟩
  rw [hKcard] at hUpper
  have hEq : (edgesInside F K).card = 2 * (K.card - 1) := by
    rw [hKcard]
    omega
  exact ⟨⟨v, by simp [namedK4Vertices]⟩, hEq⟩

/-- Source edges acquired by adjoining one vertex `u` to a vertex set `K`. -/
def newEdgesAt (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    SimpleEdgeSet V :=
  edgesInside F (insert u K) \ edgesInside F K

@[simp]
theorem mem_newEdgesAt {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    {e : SimpleEdge V} :
    e ∈ newEdgesAt F K u ↔
      e ∈ F ∧ e.vertices ⊆ insert u K ∧ ¬ e.vertices ⊆ K := by
  simp only [newEdgesAt, Finset.mem_sdiff, mem_edgesInside]
  aesop

theorem edgesInside_union_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    edgesInside F K ∪ newEdgesAt F K u = edgesInside F (insert u K) := by
  unfold newEdgesAt
  rw [Finset.union_sdiff_of_subset]
  exact edgesInside_mono_vertices F (Finset.subset_insert u K)

theorem edgesInside_disjoint_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    Disjoint (edgesInside F K) (newEdgesAt F K u) := by
  rw [Finset.disjoint_left]
  intro e heK heNew
  exact (Finset.mem_sdiff.mp heNew).2 heK

theorem card_edgesInside_add_card_newEdgesAt
    (F : SimpleEdgeSet V) (K : Finset V) (u : V) :
    (edgesInside F K).card + (newEdgesAt F K u).card =
      (edgesInside F (insert u K)).card := by
  rw [← Finset.card_union_of_disjoint
    (edgesInside_disjoint_newEdgesAt F K u)]
  exact congrArg Finset.card (edgesInside_union_newEdgesAt F K u)

/-- At most two source edges can be acquired by adding one vertex to a
tight set in a `(2,2)`-sparse graph. -/
theorem card_newEdgesAt_le_two
    {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    (hSparse : Sparse22 F) (hK : Tight22 F K) (huK : u ∉ K) :
    (newEdgesAt F K u).card ≤ 2 := by
  have hSplit := card_edgesInside_add_card_newEdgesAt F K u
  have hUpper := hSparse (insert u K) ⟨u, by simp⟩
  have hInsertCard : (insert u K).card = K.card + 1 := by
    rw [Finset.card_insert_of_notMem huK]
  rw [hK.2] at hSplit
  rw [hInsertCard] at hUpper
  have hKpos : 0 < K.card := Finset.card_pos.mpr hK.1
  omega

/-- Acquiring exactly two edges makes the one-vertex enlargement tight. -/
theorem tight22_insert_of_card_newEdgesAt_eq_two
    {F : SimpleEdgeSet V} {K : Finset V} {u : V}
    (hK : Tight22 F K) (huK : u ∉ K)
    (hTwo : (newEdgesAt F K u).card = 2) :
    Tight22 F (insert u K) := by
  refine ⟨⟨u, by simp⟩, ?_⟩
  have hSplit := card_edgesInside_add_card_newEdgesAt F K u
  have hInsertCard : (insert u K).card = K.card + 1 := by
    rw [Finset.card_insert_of_notMem huK]
  rw [hK.2, hTwo] at hSplit
  rw [hInsertCard]
  have hKpos : 0 < K.card := Finset.card_pos.mpr hK.1
  omega

/-- `K` is maximum by cardinality among proper tight supersets of the seed
`K₀` inside the active vertex set `X`. -/
structure IsMaximumProperTightSuperset
    (F : SimpleEdgeSet V) (X K₀ K : Finset V) : Prop where
  seed_subset : K₀ ⊆ K
  subset_active : K ⊆ X
  proper : K ≠ X
  tight : Tight22 F K
  card_max : ∀ {L : Finset V},
    K₀ ⊆ L → L ⊆ X → L ≠ X → Tight22 F L → L.card ≤ K.card

/-- Candidate proper tight supersets, retained as an explicit finite search
space so that maximality needs only ordinary finite classical choice. -/
noncomputable def properTightSupersets
    (F : SimpleEdgeSet V) (X K₀ : Finset V) : Finset (Finset V) := by
  classical
  exact X.powerset.filter fun K => K₀ ⊆ K ∧ K ≠ X ∧ Tight22 F K

@[simp]
theorem mem_properTightSupersets
    {F : SimpleEdgeSet V} {X K₀ K : Finset V} :
    K ∈ properTightSupersets F X K₀ ↔
      K ⊆ X ∧ K₀ ⊆ K ∧ K ≠ X ∧ Tight22 F K := by
  classical
  simp [properTightSupersets, and_left_comm]

theorem exists_isMaximumProperTightSuperset
    {F : SimpleEdgeSet V} {X K₀ : Finset V}
    (hK₀X : K₀ ⊆ X) (hK₀proper : K₀ ≠ X)
    (hK₀tight : Tight22 F K₀) :
    ∃ K : Finset V, IsMaximumProperTightSuperset F X K₀ K := by
  classical
  have hne : (properTightSupersets F X K₀).Nonempty := by
    exact ⟨K₀, mem_properTightSupersets.mpr
      ⟨hK₀X, Finset.Subset.rfl, hK₀proper, hK₀tight⟩⟩
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image (properTightSupersets F X K₀) Finset.card hne
  have hK := mem_properTightSupersets.mp hKmem
  refine ⟨K, hK.2.1, hK.1, hK.2.2.1, hK.2.2.2, ?_⟩
  intro L hseed hLX hproper htight
  exact hKmax L (mem_properTightSupersets.mpr
    ⟨hLX, hseed, hproper, htight⟩)

/-- If `K` is maximum proper tight and `K ∪ {u}` is still proper, then
`u` contributes at most one edge into `K`. -/
theorem card_newEdgesAt_le_one_of_insert_ne_active
    {F : SimpleEdgeSet V} {X K₀ K : Finset V} {u : V}
    (hSparse : Sparse22 F)
    (hK : IsMaximumProperTightSuperset F X K₀ K)
    (huX : u ∈ X) (huK : u ∉ K) (hInsertProper : insert u K ≠ X) :
    (newEdgesAt F K u).card ≤ 1 := by
  have hAtMostTwo := card_newEdgesAt_le_two hSparse hK.tight huK
  by_contra hNot
  have hTwo : (newEdgesAt F K u).card = 2 := by omega
  have hInsertTight := tight22_insert_of_card_newEdgesAt_eq_two
    hK.tight huK hTwo
  have hSeedInsert : K₀ ⊆ insert u K :=
    hK.seed_subset.trans (Finset.subset_insert u K)
  have hInsertX : insert u K ⊆ X :=
    Finset.insert_subset huX hK.subset_active
  have hCardMax := hK.card_max hSeedInsert hInsertX hInsertProper hInsertTight
  rw [Finset.card_insert_of_notMem huK] at hCardMax
  omega

/-- When the active graph is exactly `K ∪ {u}`, every edge newly
acquired by adjoining `u` is precisely an edge incident with `u`. -/
theorem incidentEdges_eq_newEdgesAt_of_active_eq_insert
    {F : SimpleEdgeSet V} {X K : Finset V} {u : V}
    (hSupported : SupportedOn F X) (huK : u ∉ K)
    (hX : X = insert u K) :
    incidentEdges F u = newEdgesAt F K u := by
  ext e
  simp only [mem_incidentEdges, mem_newEdgesAt]
  constructor
  · rintro ⟨heF, hue⟩
    refine ⟨heF, ?_, ?_⟩
    · rw [← hX]
      exact hSupported heF
    · intro heK
      exact huK (heK hue)
  · rintro ⟨heF, heInsert, heNotK⟩
    refine ⟨heF, ?_⟩
    by_contra huNot
    apply heNotK
    intro x hx
    have hxInsert := heInsert hx
    rw [Finset.mem_insert] at hxInsert
    rcases hxInsert with rfl | hxK
    · exact (huNot hx).elim
    · exact hxK

/-- A maximum proper tight module has simple external incidence unless an
outside vertex is already an inverse-Henneberg-one witness. -/
theorem exists_degree_two_or_all_outside_newEdgesAt_le_one
    {F : SimpleEdgeSet V} {X K₀ K : Finset V}
    (hG : SimpleTight22On F X)
    (hK : IsMaximumProperTightSuperset F X K₀ K) :
    (∃ u ∈ X, edgeSetDegree F u = 2) ∨
      ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1 := by
  classical
  by_cases hDegree : ∃ u ∈ X, edgeSetDegree F u = 2
  · exact Or.inl hDegree
  · refine Or.inr ?_
    intro u huX huK
    by_cases hInsert : insert u K = X
    · have hSplit := card_edgesInside_add_card_newEdgesAt F K u
      have hGlobal : F.card = 2 * (X.card - 1) := by
        rw [← edgesInside_eq_self_of_supported hG.supported]
        exact hG.tight.2
      have hInsideInsert : edgesInside F (insert u K) = F := by
        rw [hInsert]
        exact edgesInside_eq_self_of_supported hG.supported
      have hInsertCard : X.card = K.card + 1 := by
        rw [← hInsert, Finset.card_insert_of_notMem huK]
      rw [hK.tight.2, hInsideInsert, hGlobal, hInsertCard] at hSplit
      have hKpos : 0 < K.card := Finset.card_pos.mpr hK.tight.1
      have hTwo : (newEdgesAt F K u).card = 2 := by omega
      have hIncident := incidentEdges_eq_newEdgesAt_of_active_eq_insert
        hG.supported huK hInsert.symm
      exfalso
      apply hDegree
      refine ⟨u, huX, ?_⟩
      unfold edgeSetDegree
      rw [hIncident, hTwo]
    · exact card_newEdgesAt_le_one_of_insert_ne_active
        hG.sparse hK huX huK hInsert

/-- A proper tight module whose external incidence is simple after the
module is collapsed: every outside vertex is incident with at most one
source edge entering the module. -/
structure IsSimpleGraphExtensionModule
    (F : SimpleEdgeSet V) (X K : Finset V) : Prop where
  subset_active : K ⊆ X
  proper : K ≠ X
  tight : Tight22 F K
  outside_simple : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1

theorem IsMaximumProperTightSuperset.toSimpleGraphExtensionModule
    {F : SimpleEdgeSet V} {X K₀ K : Finset V}
    (hK : IsMaximumProperTightSuperset F X K₀ K)
    (hOutside : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    IsSimpleGraphExtensionModule F X K :=
  ⟨hK.subset_active, hK.proper, hK.tight, hOutside⟩

/-- The complete structural replacement for the triangle-sequence branch.
Every supported simple `(2,2)`-tight graph is either already reducible by
Henneberg 1/2, is the base `K₄`, or contains a proper tight module whose
contraction has no parallel-edge provenance collision.

The returned module contains the named `K₄` seed, so it has at least four
vertices and contraction strictly decreases the vertex count. -/
theorem hasNixonOwenReduction_or_isK4Base_or_graphExtensionModule
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨ IsK4Base F X ∨
      ∃ K : Finset V,
        IsSimpleGraphExtensionModule F X K ∧ 4 ≤ K.card := by
  rcases hasNixonOwenReduction_or_isK4Base_or_large_namedK4 hG hXcard with
      hReduce | hBase | ⟨v, _hvX, a, b, c, hNamed, hLarge⟩
  · exact Or.inl hReduce
  · exact Or.inr (Or.inl hBase)
  · let K₀ : Finset V := namedK4Vertices v a b c
    have hK₀X : K₀ ⊆ X := namedK4Vertices_subset hG hNamed
    have hK₀card : K₀.card = 4 := card_namedK4Vertices hNamed
    have hK₀proper : K₀ ≠ X := by
      intro hEq
      rw [← hEq, hK₀card] at hLarge
      omega
    have hK₀tight : Tight22 F K₀ :=
      tight22_namedK4Vertices hG.sparse hNamed
    obtain ⟨K, hKmax⟩ := exists_isMaximumProperTightSuperset
      hK₀X hK₀proper hK₀tight
    rcases exists_degree_two_or_all_outside_newEdgesAt_le_one hG hKmax with
        ⟨u, huX, huDegree⟩ | hOutside
    · exact Or.inl (hasNixonOwenReduction_of_degree_two hG huX huDegree)
    · refine Or.inr (Or.inr ⟨K,
        hKmax.toSimpleGraphExtensionModule hOutside, ?_⟩)
      rw [← hK₀card]
      exact Finset.card_le_card hKmax.seed_subset

/-! ## Provenance partition for a tight-module contraction -/

/-- All source edges from vertices in `U` into the module `K`. -/
def crossEdgesTo (F : SimpleEdgeSet V) (K U : Finset V) :
    SimpleEdgeSet V :=
  U.biUnion fun u => newEdgesAt F K u

@[simp]
theorem mem_crossEdgesTo {F : SimpleEdgeSet V} {K U : Finset V}
    {e : SimpleEdge V} :
    e ∈ crossEdgesTo F K U ↔ ∃ u ∈ U, e ∈ newEdgesAt F K u := by
  simp [crossEdgesTo]

theorem disjoint_newEdgesAt_of_ne
    {F : SimpleEdgeSet V} {K : Finset V} {u w : V}
    (huw : u ≠ w) :
    Disjoint (newEdgesAt F K u) (newEdgesAt F K w) := by
  rw [Finset.disjoint_left]
  intro e heu hew
  have heu' := mem_newEdgesAt.mp heu
  have hew' := mem_newEdgesAt.mp hew
  have hExists : ∃ x ∈ e.vertices, x ∉ K := by
    by_contra hNot
    apply heu'.2.2
    intro x hx
    by_contra hxK
    exact hNot ⟨x, hx, hxK⟩
  obtain ⟨x, hxe, hxK⟩ := hExists
  have hxu : x = u := by
    rcases Finset.mem_insert.mp (heu'.2.1 hxe) with hxu | hxK'
    · exact hxu
    · exact (hxK hxK').elim
  have hxw : x = w := by
    rcases Finset.mem_insert.mp (hew'.2.1 hxe) with hxw | hxK'
    · exact hxw
    · exact (hxK hxK').elim
  exact huw (hxu.symm.trans hxw)

theorem pairwiseDisjoint_newEdgesAt
    {F : SimpleEdgeSet V} {K U : Finset V} (_hUK : Disjoint U K) :
    (U : Set V).PairwiseDisjoint fun u => newEdgesAt F K u := by
  intro u huU w hwU huw
  exact disjoint_newEdgesAt_of_ne huw

theorem card_crossEdgesTo
    {F : SimpleEdgeSet V} {K U : Finset V} (hUK : Disjoint U K) :
    (crossEdgesTo F K U).card = ∑ u ∈ U, (newEdgesAt F K u).card := by
  unfold crossEdgesTo
  exact Finset.card_biUnion (pairwiseDisjoint_newEdgesAt hUK)

theorem internalEdges_disjoint_crossEdgesTo
    (F : SimpleEdgeSet V) (K U : Finset V) :
    Disjoint (edgesInside F K) (crossEdgesTo F K U) := by
  rw [Finset.disjoint_left]
  intro e heK heCross
  obtain ⟨u, _huU, heu⟩ := mem_crossEdgesTo.mp heCross
  exact (mem_newEdgesAt.mp heu).2.2 (mem_edgesInside.mp heK).2

theorem internalEdges_disjoint_exteriorEdges
    (F : SimpleEdgeSet V) {K U : Finset V} (hUK : Disjoint U K) :
    Disjoint (edgesInside F K) (edgesInside F U) := by
  rw [Finset.disjoint_left]
  intro e heK heU
  have hne : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
  obtain ⟨x, hxe⟩ := hne
  exact (Finset.disjoint_left.mp hUK)
    ((mem_edgesInside.mp heU).2 hxe) ((mem_edgesInside.mp heK).2 hxe)

theorem exteriorEdges_disjoint_newEdgesAt
    {F : SimpleEdgeSet V} {K U : Finset V} {u : V}
    (hUK : Disjoint U K) (_huU : u ∈ U) :
    Disjoint (edgesInside F U) (newEdgesAt F K u) := by
  rw [Finset.disjoint_left]
  intro e heU heNew
  have hUsub := (mem_edgesInside.mp heU).2
  have hNew := mem_newEdgesAt.mp heNew
  have hAllU : e.vertices ⊆ ({u} : Finset V) := by
    intro x hx
    have hxU := hUsub hx
    rcases Finset.mem_insert.mp (hNew.2.1 hx) with hxu | hxK
    · simp [hxu]
    · exact (Finset.disjoint_left.mp hUK hxU hxK).elim
  have hCardLe : e.vertices.card ≤ ({u} : Finset V).card :=
    Finset.card_le_card hAllU
  rw [e.card_vertices] at hCardLe
  simp at hCardLe

theorem exteriorEdges_disjoint_crossEdgesTo
    (F : SimpleEdgeSet V) {K U : Finset V} (hUK : Disjoint U K) :
    Disjoint (edgesInside F U) (crossEdgesTo F K U) := by
  rw [Finset.disjoint_left]
  intro e heU heCross
  obtain ⟨u, huU, heNew⟩ := mem_crossEdgesTo.mp heCross
  exact (Finset.disjoint_left.mp
    (exteriorEdges_disjoint_newEdgesAt (F := F) hUK huU)) heU heNew

theorem module_exterior_cross_union_subset
    {F : SimpleEdgeSet V} {K U : Finset V} :
    edgesInside F K ∪ edgesInside F U ∪ crossEdgesTo F K U ⊆
      edgesInside F (K ∪ U) := by
  intro e he
  rw [Finset.mem_union] at he
  rcases he with heInternalOrExterior | heCross
  · rw [Finset.mem_union] at heInternalOrExterior
    rcases heInternalOrExterior with heK | heU
    · exact edgesInside_mono_vertices F Finset.subset_union_left heK
    · exact edgesInside_mono_vertices F Finset.subset_union_right heU
  · obtain ⟨u, huU, heNew⟩ := mem_crossEdgesTo.mp heCross
    have hNew := mem_newEdgesAt.mp heNew
    apply mem_edgesInside.mpr
    refine ⟨hNew.1, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp (hNew.2.1 hx) with rfl | hxK
    · exact Finset.mem_union_right K huU
    · exact Finset.mem_union_left U hxK

/-- Exact lower-bound packet used in the quotient sparsity proof: internal
module edges, exterior edges and all provenance-labelled crossing edges
are pairwise disjoint source edges inside `K ∪ U`. -/
theorem card_module_add_exterior_add_cross_le
    {F : SimpleEdgeSet V} {K U : Finset V} (hUK : Disjoint U K) :
    (edgesInside F K).card + (edgesInside F U).card +
        (crossEdgesTo F K U).card ≤
      (edgesInside F (K ∪ U)).card := by
  have hInternalExterior := internalEdges_disjoint_exteriorEdges F hUK
  have hUnionCross :
      Disjoint (edgesInside F K ∪ edgesInside F U)
        (crossEdgesTo F K U) := by
    rw [Finset.disjoint_left]
    intro e heUnion heCross
    rw [Finset.mem_union] at heUnion
    rcases heUnion with heK | heU
    · exact (Finset.disjoint_left.mp
        (internalEdges_disjoint_crossEdgesTo F K U)) heK heCross
    · exact (Finset.disjoint_left.mp
        (exteriorEdges_disjoint_crossEdgesTo F hUK)) heU heCross
  calc
    (edgesInside F K).card + (edgesInside F U).card +
          (crossEdgesTo F K U).card =
        ((edgesInside F K ∪ edgesInside F U) ∪
          crossEdgesTo F K U).card := by
      rw [Finset.card_union_of_disjoint hUnionCross,
        Finset.card_union_of_disjoint hInternalExterior]
    _ ≤ (edgesInside F (K ∪ U)).card :=
      Finset.card_le_card module_exterior_cross_union_subset

/-! ## Explicit simple quotient edge set -/

/-- Collapsing `K` to `r` sends an outside vertex to the simple edge
joining it to `r`. -/
def collapsedBoundaryEmbedding
    (K U : Finset V) (r : V) (hrK : r ∈ K) (hUK : Disjoint U K) :
    {u // u ∈ U} ↪ SimpleEdge V where
  toFun u := simpleEdge r u.1 (by
    intro hru
    exact (Finset.disjoint_left.mp hUK u.2 (hru ▸ hrK)))
  inj' := by
    intro u w huw
    apply Subtype.ext
    have hEdge := congrArg Subtype.val huw
    change s(r, u.1) = s(r, w.1) at hEdge
    rw [Sym2.eq_iff] at hEdge
    rcases hEdge with hEdge | hEdge
    · exact hEdge.2
    · exfalso
      exact (Finset.disjoint_left.mp hUK u.2 (hEdge.2.symm ▸ hrK))

/-- Quotient boundary edges, one for each outside vertex with nonempty
source provenance into `K`. -/
noncomputable def collapsedBoundaryEdges
    (F : SimpleEdgeSet V) (K U : Finset V) (r : V)
    (hrK : r ∈ K) (hUK : Disjoint U K) : SimpleEdgeSet V := by
  classical
  exact (U.attach.filter fun u => (newEdgesAt F K u.1).Nonempty).map
    (collapsedBoundaryEmbedding K U r hrK hUK)

@[simp]
theorem mem_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    {hrK : r ∈ K} {hUK : Disjoint U K} {e : SimpleEdge V} :
    e ∈ collapsedBoundaryEdges F K U r hrK hUK ↔
      ∃ u : V, u ∈ U ∧ (newEdgesAt F K u).Nonempty ∧
        ∃ hru : r ≠ u, e = simpleEdge r u hru := by
  classical
  simp only [collapsedBoundaryEdges, Finset.mem_map, Finset.mem_filter,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨u, ⟨huNew, rfl⟩⟩
    refine ⟨u.1, u.2, huNew, ?_⟩
    refine ⟨?_, rfl⟩
    intro hru
    exact (Finset.disjoint_left.mp hUK u.2 (hru ▸ hrK))
  · rintro ⟨u, huU, huNew, hru, rfl⟩
    refine ⟨⟨u, huU⟩, ⟨huNew, ?_⟩⟩
    apply Subtype.ext
    simp [collapsedBoundaryEmbedding, simpleEdge]

theorem card_filter_nonempty_eq_sum_card_of_le_one
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : A → Finset B)
    (hOne : ∀ a ∈ S, (T a).card ≤ 1) :
    (S.filter fun a => (T a).Nonempty).card = ∑ a ∈ S, (T a).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hOneS : ∀ x ∈ S, (T x).card ≤ 1 := by
        intro x hx
        exact hOne x (Finset.mem_insert_of_mem hx)
      have ih' := ih hOneS
      have hOneA := hOne a (by simp)
      by_cases hne : (T a).Nonempty
      · have hCardA : (T a).card = 1 := by
          have hpos : 0 < (T a).card := Finset.card_pos.mpr hne
          omega
        have haFilter : a ∉ S.filter fun x => (T x).Nonempty := by
          simp [ha]
        rw [Finset.filter_insert, if_pos hne,
          Finset.card_insert_of_notMem haFilter, Finset.sum_insert ha,
          hCardA, ih']
        omega
      · have hCardA : (T a).card = 0 := by
          exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
        rw [Finset.filter_insert, if_neg hne, Finset.sum_insert ha,
          hCardA, ih']
        omega

theorem card_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    (hrK : r ∈ K) (hUK : Disjoint U K)
    (hOne : ∀ u ∈ U, (newEdgesAt F K u).card ≤ 1) :
    (collapsedBoundaryEdges F K U r hrK hUK).card =
      (crossEdgesTo F K U).card := by
  classical
  have hAttachCard :
      (U.attach.filter fun u => (newEdgesAt F K u.1).Nonempty).card =
        (U.filter fun u => (newEdgesAt F K u).Nonempty).card := by
    apply Finset.card_bij (fun u _hu => u.1)
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨u.2, hu'.2⟩
    · intro u₁ _hu₁ u₂ _hu₂ hval
      exact Subtype.ext hval
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      refine ⟨⟨u, hu'.1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp, hu'.2⟩
  rw [collapsedBoundaryEdges, Finset.card_map, hAttachCard,
    card_crossEdgesTo hUK]
  exact card_filter_nonempty_eq_sum_card_of_le_one U
    (newEdgesAt F K) hOne

theorem exteriorEdges_disjoint_collapsedBoundaryEdges
    {F : SimpleEdgeSet V} {K U : Finset V} {r : V}
    (hrK : r ∈ K) (hUK : Disjoint U K) :
    Disjoint (edgesInside F U)
      (collapsedBoundaryEdges F K U r hrK hUK) := by
  rw [Finset.disjoint_left]
  intro e heExterior heBoundary
  obtain ⟨u, huU, _huNew, hru, rfl⟩ :=
    mem_collapsedBoundaryEdges.mp heBoundary
  have hrVertices : r ∈ (simpleEdge r u hru).vertices := by
    rw [vertices_simpleEdge]
    simp
  have hrU := (mem_edgesInside.mp heExterior).2 hrVertices
  exact (Finset.disjoint_left.mp hUK hrU hrK)

/-- The explicit simple graph obtained by collapsing `K` to `r`: exterior
source edges are retained, while all source edges entering `K` at one
outside vertex are represented by the single edge to `r`. -/
noncomputable def graphExtensionQuotientEdges
    (F : SimpleEdgeSet V) (X K : Finset V) (r : V) (hrK : r ∈ K) :
    SimpleEdgeSet V := by
  classical
  let U := X \ K
  exact edgesInside F U ∪
    collapsedBoundaryEdges F K U r hrK (Finset.sdiff_disjoint)

/-- Active vertices after collapsing `K` to its retained representative. -/
def graphExtensionQuotientVertices (X K : Finset V) (r : V) : Finset V :=
  insert r (X \ K)

theorem graphExtensionQuotientEdges_supported
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V} (hrK : r ∈ K) :
    SupportedOn (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) := by
  intro e he
  rw [graphExtensionQuotientEdges, Finset.mem_union] at he
  rcases he with heExterior | heBoundary
  · exact (mem_edgesInside.mp heExterior).2.trans
      (Finset.subset_insert r (X \ K))
  · obtain ⟨u, huU, _huNew, hru, rfl⟩ :=
      mem_collapsedBoundaryEdges.mp heBoundary
    rw [vertices_simpleEdge]
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem huU

/-- Every supported source edge is uniquely classified as internal to the
module, exterior to it, or crossing from one outside vertex into it. -/
theorem module_exterior_cross_union_eq
    {F : SimpleEdgeSet V} {X K : Finset V}
    (hSupported : SupportedOn F X) (_hKX : K ⊆ X) :
    edgesInside F K ∪ edgesInside F (X \ K) ∪
        crossEdgesTo F K (X \ K) = F := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [Finset.mem_union] at he
    rcases he with heInternalOrExterior | heCross
    · rw [Finset.mem_union] at heInternalOrExterior
      rcases heInternalOrExterior with heK | heU
      · exact (mem_edgesInside.mp heK).1
      · exact (mem_edgesInside.mp heU).1
    · obtain ⟨u, _huU, heNew⟩ := mem_crossEdgesTo.mp heCross
      exact (mem_newEdgesAt.mp heNew).1
  · intro e heF
    have heX := hSupported heF
    have hVerticesNonempty : e.vertices.Nonempty :=
      Finset.card_pos.mp (by simp)
    by_cases heK : e.vertices ⊆ K
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_edgesInside.mpr ⟨heF, heK⟩))
    · have hOutside : ∃ x ∈ e.vertices, x ∉ K := by
        by_contra hNot
        apply heK
        intro x hx
        by_contra hxK
        exact hNot ⟨x, hx, hxK⟩
      obtain ⟨x, hxEdge, hxK⟩ := hOutside
      obtain ⟨a, hxa, heEq⟩ := exists_otherEndpoint e hxEdge
      have hxX : x ∈ X := heX hxEdge
      have haEdge : a ∈ e.vertices := by
        rw [heEq, vertices_simpleEdge]
        simp
      have haX : a ∈ X := heX haEdge
      have hxU : x ∈ X \ K := Finset.mem_sdiff.mpr ⟨hxX, hxK⟩
      by_cases haK : a ∈ K
      · apply Finset.mem_union_right
        apply mem_crossEdgesTo.mpr
        refine ⟨x, hxU, ?_⟩
        apply mem_newEdgesAt.mpr
        refine ⟨heF, ?_, heK⟩
        rw [heEq, vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem haK
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply mem_edgesInside.mpr
        refine ⟨heF, ?_⟩
        rw [heEq, vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hxU
        · exact Finset.mem_sdiff.mpr ⟨haX, haK⟩

/-- Global edge count of the explicit quotient. -/
theorem card_graphExtensionQuotientEdges
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hSupported : SupportedOn F X) (hKX : K ⊆ X) (hrK : r ∈ K)
    (hOne : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    (graphExtensionQuotientEdges F X K r hrK).card +
        (edgesInside F K).card = F.card := by
  let U := X \ K
  have hUK : Disjoint U K := Finset.sdiff_disjoint
  have hOneU : ∀ u ∈ U, (newEdgesAt F K u).card ≤ 1 := by
    intro u huU
    exact hOne u (Finset.mem_sdiff.mp huU).1 (Finset.mem_sdiff.mp huU).2
  have hBoundaryCard := card_collapsedBoundaryEdges hrK hUK hOneU
  have hExteriorBoundary :=
    exteriorEdges_disjoint_collapsedBoundaryEdges (F := F) hrK hUK
  have hInternalExterior := internalEdges_disjoint_exteriorEdges F hUK
  have hInternalCross := internalEdges_disjoint_crossEdgesTo F K U
  have hExteriorCross := exteriorEdges_disjoint_crossEdgesTo F hUK
  have hSourceUnion :
      edgesInside F K ∪ edgesInside F U ∪ crossEdgesTo F K U = F := by
    exact module_exterior_cross_union_eq hSupported hKX
  have hSourceUnionDisjoint :
      Disjoint (edgesInside F K ∪ edgesInside F U) (crossEdgesTo F K U) := by
    rw [Finset.disjoint_left]
    intro e heUnion heCross
    rw [Finset.mem_union] at heUnion
    rcases heUnion with heK | heU
    · exact (Finset.disjoint_left.mp hInternalCross) heK heCross
    · exact (Finset.disjoint_left.mp hExteriorCross) heU heCross
  have hSourceCard :
      (edgesInside F K).card + (edgesInside F U).card +
          (crossEdgesTo F K U).card = F.card := by
    calc
      (edgesInside F K).card + (edgesInside F U).card +
            (crossEdgesTo F K U).card =
          ((edgesInside F K ∪ edgesInside F U) ∪
            crossEdgesTo F K U).card := by
        rw [Finset.card_union_of_disjoint hSourceUnionDisjoint,
          Finset.card_union_of_disjoint hInternalExterior]
      _ = F.card := congrArg Finset.card hSourceUnion
  have hQuotientCard :
      (graphExtensionQuotientEdges F X K r hrK).card =
        (edgesInside F U).card + (crossEdgesTo F K U).card := by
    rw [graphExtensionQuotientEdges,
      Finset.card_union_of_disjoint hExteriorBoundary, hBoundaryCard]
  rw [hQuotientCard]
  omega

theorem card_graphExtensionQuotientVertices
    {X K : Finset V} {r : V} (hKX : K ⊆ X) (hrK : r ∈ K) :
    (graphExtensionQuotientVertices X K r).card = X.card - K.card + 1 := by
  have hrNot : r ∉ X \ K := by simp [hrK]
  rw [graphExtensionQuotientVertices, Finset.card_insert_of_notMem hrNot,
    Finset.card_sdiff_of_subset hKX]

/-- Once quotient sparsity is available, global tightness follows by exact
subtraction of the tight module's internal edge count.  This lemma is kept
separate because the same count identity is also used by the null-cellule
dimension induction. -/
theorem graphExtensionQuotient_tight
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X) (hModule : IsSimpleGraphExtensionModule F X K)
    (hrK : r ∈ K) :
    Tight22 (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) := by
  refine ⟨⟨r, by simp [graphExtensionQuotientVertices]⟩, ?_⟩
  rw [edgesInside_eq_self_of_supported
    (graphExtensionQuotientEdges_supported hrK)]
  have hCard := card_graphExtensionQuotientEdges hG.supported
    hModule.subset_active hrK hModule.outside_simple
  have hGlobal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hVertices := card_graphExtensionQuotientVertices
    hModule.subset_active hrK
  rw [hModule.tight.2, hGlobal] at hCard
  rw [hVertices]
  have hKpos : 0 < K.card := Finset.card_pos.mpr hModule.tight.1
  have hKle : K.card ≤ X.card :=
    Finset.card_le_card hModule.subset_active
  omega

/-! ## Subset lifting and quotient sparsity -/

/-- Outside vertices of a quotient test set, with the retained module
representative removed. -/
def quotientOutsideSubset (Y X K : Finset V) (r : V) : Finset V :=
  Y.erase r ∩ (X \ K)

theorem quotientOutsideSubset_subset_Y
    (Y X K : Finset V) (r : V) :
    quotientOutsideSubset Y X K r ⊆ Y := by
  intro u hu
  exact (Finset.mem_erase.mp (Finset.mem_inter.mp hu).1).2

theorem quotientOutsideSubset_subset_outside
    (Y X K : Finset V) (r : V) :
    quotientOutsideSubset Y X K r ⊆ X \ K := by
  intro u hu
  exact (Finset.mem_inter.mp hu).2

theorem quotientOutsideSubset_disjoint
    (Y X K : Finset V) (r : V) :
    Disjoint (quotientOutsideSubset Y X K r) K :=
  (Finset.disjoint_of_subset_left
    (quotientOutsideSubset_subset_outside Y X K r)
    Finset.sdiff_disjoint)

theorem edgesInside_exterior_eq_quotientOutsideSubset
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V} (hrK : r ∈ K) :
    edgesInside (edgesInside F (X \ K)) Y =
      edgesInside F (quotientOutsideSubset Y X K r) := by
  ext e
  simp only [mem_edgesInside]
  constructor
  · rintro ⟨⟨heF, heOutside⟩, heY⟩
    refine ⟨heF, ?_⟩
    intro u huEdge
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, heY huEdge⟩, heOutside huEdge⟩
    intro hur
    subst u
    exact (Finset.mem_sdiff.mp (heOutside huEdge)).2 hrK
  · rintro ⟨heF, heLift⟩
    refine ⟨⟨heF, ?_⟩, ?_⟩
    · intro u huEdge
      exact (Finset.mem_inter.mp (heLift huEdge)).2
    · intro u huEdge
      exact (Finset.mem_erase.mp
        (Finset.mem_inter.mp (heLift huEdge)).1).2

theorem edgesInside_collapsedBoundaryEdges_eq_of_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∈ Y) :
    edgesInside
        (collapsedBoundaryEdges F K (X \ K) r hrK Finset.sdiff_disjoint) Y =
      collapsedBoundaryEdges F K (quotientOutsideSubset Y X K r) r hrK
        (quotientOutsideSubset_disjoint Y X K r) := by
  ext e
  constructor
  · intro he
    have he' := mem_edgesInside.mp he
    obtain ⟨u, huOutside, huNew, hru, heEq⟩ :=
      mem_collapsedBoundaryEdges.mp he'.1
    apply mem_collapsedBoundaryEdges.mpr
    refine ⟨u, ?_, huNew, hru, heEq⟩
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hru, ?_⟩, huOutside⟩
    have huVertices : u ∈ (simpleEdge r u hru).vertices := by
      rw [vertices_simpleEdge]
      simp
    exact he'.2 (heEq.symm ▸ huVertices)
  · intro he
    obtain ⟨u, huLift, huNew, hru, heEq⟩ :=
      mem_collapsedBoundaryEdges.mp he
    apply mem_edgesInside.mpr
    refine ⟨?_, ?_⟩
    · apply mem_collapsedBoundaryEdges.mpr
      exact ⟨u, (Finset.mem_inter.mp huLift).2, huNew, hru, heEq⟩
    · rw [heEq, vertices_simpleEdge]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hrY
      · exact (Finset.mem_erase.mp (Finset.mem_inter.mp huLift).1).2

theorem edgesInside_collapsedBoundaryEdges_eq_empty_of_not_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∉ Y) :
    edgesInside
      (collapsedBoundaryEdges F K (X \ K) r hrK Finset.sdiff_disjoint) Y =
      ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨e, he⟩ := hne
  have he' := mem_edgesInside.mp he
  obtain ⟨u, _huOutside, _huNew, hru, heEq⟩ :=
    mem_collapsedBoundaryEdges.mp he'.1
  apply hrY
  have hrVertices : r ∈ (simpleEdge r u hru).vertices := by
    rw [vertices_simpleEdge]
    simp
  exact he'.2 (heEq.symm ▸ hrVertices)

theorem edgesInside_union_edges
    (A B : SimpleEdgeSet V) (Y : Finset V) :
    edgesInside (A ∪ B) Y = edgesInside A Y ∪ edgesInside B Y := by
  ext e
  simp only [mem_edgesInside, Finset.mem_union]
  aesop

theorem card_edgesInside_graphExtensionQuotient_of_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∈ Y)
    (hOne : ∀ u ∈ X, u ∉ K → (newEdgesAt F K u).card ≤ 1) :
    (edgesInside (graphExtensionQuotientEdges F X K r hrK) Y).card =
      (edgesInside F (quotientOutsideSubset Y X K r)).card +
        (crossEdgesTo F K (quotientOutsideSubset Y X K r)).card := by
  let UY := quotientOutsideSubset Y X K r
  have hUYdisjoint : Disjoint UY K := quotientOutsideSubset_disjoint Y X K r
  have hOneUY : ∀ u ∈ UY, (newEdgesAt F K u).card ≤ 1 := by
    intro u huUY
    have huOutside := quotientOutsideSubset_subset_outside Y X K r huUY
    exact hOne u (Finset.mem_sdiff.mp huOutside).1
      (Finset.mem_sdiff.mp huOutside).2
  have hDisjoint := exteriorEdges_disjoint_collapsedBoundaryEdges
    (F := F) hrK hUYdisjoint
  rw [graphExtensionQuotientEdges,
    edgesInside_union_edges,
    edgesInside_exterior_eq_quotientOutsideSubset hrK,
    edgesInside_collapsedBoundaryEdges_eq_of_mem hrK hrY,
    Finset.card_union_of_disjoint hDisjoint,
    card_collapsedBoundaryEdges hrK hUYdisjoint hOneUY]

theorem card_edgesInside_graphExtensionQuotient_of_not_mem
    {F : SimpleEdgeSet V} {Y X K : Finset V} {r : V}
    (hrK : r ∈ K) (hrY : r ∉ Y) :
    (edgesInside (graphExtensionQuotientEdges F X K r hrK) Y).card =
      (edgesInside F (quotientOutsideSubset Y X K r)).card := by
  rw [graphExtensionQuotientEdges,
    edgesInside_union_edges,
    edgesInside_exterior_eq_quotientOutsideSubset hrK,
    edgesInside_collapsedBoundaryEdges_eq_empty_of_not_mem hrK hrY]
  simp

/-- Every induced quotient edge set obeys the `(2,2)` count.  A set
containing the collapse point is lifted to
`K ∪ U`, and the exact tight count of `K` is subtracted from the source
sparsity inequality. -/
theorem graphExtensionQuotient_sparse
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K) (hrK : r ∈ K) :
    Sparse22 (graphExtensionQuotientEdges F X K r hrK) := by
  intro Y hY
  let UY := quotientOutsideSubset Y X K r
  have hUYdisjoint : Disjoint UY K := quotientOutsideSubset_disjoint Y X K r
  have hUYsubsetY : UY ⊆ Y := quotientOutsideSubset_subset_Y Y X K r
  by_cases hrY : r ∈ Y
  · rw [card_edgesInside_graphExtensionQuotient_of_mem
      hrK hrY hModule.outside_simple]
    change (edgesInside F UY).card + (crossEdgesTo F K UY).card ≤
      2 * (Y.card - 1)
    have hPacket := card_module_add_exterior_add_cross_le
      (F := F) hUYdisjoint
    have hLiftNonempty : (K ∪ UY).Nonempty :=
      hModule.tight.1.mono Finset.subset_union_left
    have hSourceUpper := hG.sparse (K ∪ UY) hLiftNonempty
    have hUnionCard : (K ∪ UY).card = K.card + UY.card := by
      rw [Finset.card_union_of_disjoint hUYdisjoint.symm]
    rw [hModule.tight.2] at hPacket
    rw [hUnionCard] at hSourceUpper
    have hEraseCard : (Y.erase r).card = Y.card - 1 :=
      Finset.card_erase_of_mem hrY
    have hUYsubsetErase : UY ⊆ Y.erase r := by
      intro u hu
      exact (Finset.mem_inter.mp hu).1
    have hUYcard : UY.card ≤ Y.card - 1 := by
      rw [← hEraseCard]
      exact Finset.card_le_card hUYsubsetErase
    have hKpos : 0 < K.card := Finset.card_pos.mpr hModule.tight.1
    omega
  · rw [card_edgesInside_graphExtensionQuotient_of_not_mem hrK hrY]
    change (edgesInside F UY).card ≤ 2 * (Y.card - 1)
    by_cases hUYne : UY.Nonempty
    · have hUpper := hG.sparse UY hUYne
      have hUYcard : UY.card ≤ Y.card :=
        Finset.card_le_card hUYsubsetY
      have hYpos : 0 < Y.card := Finset.card_pos.mpr hY
      omega
    · have hUYempty : UY = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUYne
      rw [hUYempty]
      have hEdgesEmpty : edgesInside F (∅ : Finset V) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨e, he⟩ := hne
        have hSub := (mem_edgesInside.mp he).2
        have hCardLe := Finset.card_le_card hSub
        rw [e.card_vertices] at hCardLe
        simp at hCardLe
      rw [hEdgesEmpty]
      simp

/-- The explicit contraction of a simple graph-extension module is again
a supported simple `(2,2)`-tight graph. -/
theorem graphExtensionQuotient_simpleTight22On
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K) (hrK : r ∈ K) :
    SimpleTight22On (graphExtensionQuotientEdges F X K r hrK)
      (graphExtensionQuotientVertices X K r) :=
  ⟨graphExtensionQuotientEdges_supported hrK,
    graphExtensionQuotient_sparse hG hModule hrK,
    graphExtensionQuotient_tight hG hModule hrK⟩

theorem graphExtensionQuotientVertices_card_lt
    {X K : Finset V} {r : V} (hKX : K ⊆ X) (hrK : r ∈ K)
    (hKcard : 2 ≤ K.card) :
    (graphExtensionQuotientVertices X K r).card < X.card := by
  rw [card_graphExtensionQuotientVertices hKX hrK]
  have hKle : K.card ≤ X.card := Finset.card_le_card hKX
  omega

/-! ## Closed extended reduction theorem -/

/-- Exact inverse graph-extension surgery: a proper tight module `K` is
replaced by one retained representative `r`, with quotient edges given by
the explicit provenance construction above. -/
def IsInverseGraphExtension
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ K : Finset V, ∃ r : V, ∃ hrK : r ∈ K,
    IsSimpleGraphExtensionModule F X K ∧
      X' = graphExtensionQuotientVertices X K r ∧
      F' = graphExtensionQuotientEdges F X K r hrK

/-- An inverse graph-extension whose explicit quotient remains supported
simple `(2,2)`-tight. -/
def LegalInverseGraphExtension
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseGraphExtension F X F' X' ∧ SimpleTight22On F' X'

/-- The reduction class naturally suited to the bulk--interface induction:
the four Nixon--Owen local moves are retained, but an arbitrary proper
tight module may also be contracted in one exact graph-extension step. -/
def HasNixonOwenOrGraphExtensionReduction
    (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  HasNixonOwenReduction F X ∨
    ∃ F' : SimpleEdgeSet V, ∃ X' : Finset V,
      X'.card < X.card ∧ LegalInverseGraphExtension F X F' X'

theorem legalInverseGraphExtension_of_module
    {F : SimpleEdgeSet V} {X K : Finset V}
    (hG : SimpleTight22On F X)
    (hModule : IsSimpleGraphExtensionModule F X K)
    (hKcard : 2 ≤ K.card) :
    ∃ r : V, ∃ hrK : r ∈ K,
      (graphExtensionQuotientVertices X K r).card < X.card ∧
      LegalInverseGraphExtension F X
        (graphExtensionQuotientEdges F X K r hrK)
        (graphExtensionQuotientVertices X K r) := by
  obtain ⟨r, hrK⟩ := hModule.tight.1
  refine ⟨r, hrK,
    graphExtensionQuotientVertices_card_lt hModule.subset_active hrK hKcard,
    ?_, graphExtensionQuotient_simpleTight22On hG hModule hrK⟩
  exact ⟨K, r, hrK, hModule, rfl, rfl⟩

/-- End-to-end closure of the simple `(2,2)`-tight combinatorial reduction
stage without triangle sequences.  Every graph with at least two active
vertices is either the exact `K₄` base or has a strictly smaller legal
reduction, where the additional graph-extension case is an explicit
supported sparse-and-tight quotient. -/
theorem isK4Base_or_hasNixonOwenOrGraphExtensionReduction
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    IsK4Base F X ∨ HasNixonOwenOrGraphExtensionReduction F X := by
  rcases hasNixonOwenReduction_or_isK4Base_or_graphExtensionModule
      hG hXcard with hReduce | hBase | ⟨K, hModule, hKcard⟩
  · exact Or.inr (Or.inl hReduce)
  · exact Or.inl hBase
  · have hKtwo : 2 ≤ K.card := by omega
    obtain ⟨r, hrK, hCard, hLegal⟩ :=
      legalInverseGraphExtension_of_module hG hModule hKtwo
    exact Or.inr (Or.inr ⟨_, _, hCard, hLegal⟩)

/-! ## Agreement with the ordinary simple push-forward semantics -/

theorem Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
    (z : Sym2 V) {X K : Finset V} {r : V}
    (hz : z.toFinset ⊆ X \ K) :
    z.map (collapseSet K r) = z := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      have ha : a ∈ X \ K := hz (by simp [Sym2.toFinset_mk_eq])
      have hb : b ∈ X \ K := hz (by simp [Sym2.toFinset_mk_eq])
      simp [Sym2.map_mk, collapseSet,
        (Finset.mem_sdiff.mp ha).2, (Finset.mem_sdiff.mp hb).2]

theorem Sym2.isDiag_map_collapseSet_of_toFinset_subset
    (z : Sym2 V) {K : Finset V} {r : V}
    (hz : z.toFinset ⊆ K) :
    (z.map (collapseSet K r)).IsDiag := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      have ha : a ∈ K := hz (by simp [Sym2.toFinset_mk_eq])
      have hb : b ∈ K := hz (by simp [Sym2.toFinset_mk_eq])
      simp [Sym2.map_mk, collapseSet, ha, hb, Sym2.mk_isDiag_iff]

/-- A provenance edge entering `K` at the outside vertex `u` maps to the
single quotient boundary edge `ru`. -/
theorem exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt
    {F : SimpleEdgeSet V} {K : Finset V} {r u : V}
    (hrK : r ∈ K) (huK : u ∉ K) {e : SimpleEdge V}
    (heNew : e ∈ newEdgesAt F K u) :
    ∃ hru : r ≠ u,
      (simpleEdge r u hru).1 = e.1.map (collapseSet K r) := by
  have hNew := mem_newEdgesAt.mp heNew
  have hOutside : ∃ x ∈ e.vertices, x ∉ K := by
    by_contra hNot
    apply hNew.2.2
    intro x hx
    by_contra hxK
    exact hNot ⟨x, hx, hxK⟩
  obtain ⟨x, hxEdge, hxK⟩ := hOutside
  have hxu : x = u := by
    rcases Finset.mem_insert.mp (hNew.2.1 hxEdge) with hxu | hxK'
    · exact hxu
    · exact (hxK hxK').elim
  have huEdge : u ∈ e.vertices := hxu ▸ hxEdge
  obtain ⟨a, hua, heEq⟩ := exists_otherEndpoint e huEdge
  have haEdge : a ∈ e.vertices := by
    rw [heEq, vertices_simpleEdge]
    simp
  have haK : a ∈ K := by
    rcases Finset.mem_insert.mp (hNew.2.1 haEdge) with hau | haK
    · exact (hua hau.symm).elim
    · exact haK
  have hru : r ≠ u := by
    intro hru
    exact huK (hru ▸ hrK)
  refine ⟨hru, ?_⟩
  rw [heEq]
  simp [simpleEdge, Sym2.map_mk, collapseSet, huK, haK]

/-- The explicit quotient edge set is extensionally the ordinary simple
push-forward of the source edge set along `collapseSet`.  Thus the custom
provenance presentation above is not a surrogate notion of contraction. -/
theorem graphExtensionQuotientEdges_isSimpleEdgePushForward
    {F : SimpleEdgeSet V} {X K : Finset V} {r : V}
    (hSupported : SupportedOn F X) (hKX : K ⊆ X) (hrK : r ∈ K) :
    IsSimpleEdgePushForward (collapseSet K r) F
      (graphExtensionQuotientEdges F X K r hrK) := by
  intro e'
  constructor
  · intro he'
    rw [graphExtensionQuotientEdges, Finset.mem_union] at he'
    rcases he' with heExterior | heBoundary
    · refine ⟨e', (mem_edgesInside.mp heExterior).1, ?_⟩
      exact (Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
        e'.1 (mem_edgesInside.mp heExterior).2).symm
    · obtain ⟨u, huOutside, huNew, hru, heEq⟩ :=
        mem_collapsedBoundaryEdges.mp heBoundary
      obtain ⟨e, heNew⟩ := huNew
      have huK : u ∉ K := (Finset.mem_sdiff.mp huOutside).2
      obtain ⟨hru', hMap⟩ :=
        exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt
          hrK huK heNew
      refine ⟨e, (mem_newEdgesAt.mp heNew).1, ?_⟩
      calc
        e'.1 = (simpleEdge r u hru).1 := congrArg Subtype.val heEq
        _ = (simpleEdge r u hru').1 := by rfl
        _ = e.1.map (collapseSet K r) := hMap
  · rintro ⟨e, heF, heImage⟩
    have hClass : e ∈
        edgesInside F K ∪ edgesInside F (X \ K) ∪
          crossEdgesTo F K (X \ K) := by
      rw [module_exterior_cross_union_eq hSupported hKX]
      exact heF
    rw [Finset.mem_union] at hClass
    rcases hClass with hInternalOrExterior | hCross
    · rw [Finset.mem_union] at hInternalOrExterior
      rcases hInternalOrExterior with hInternal | hExterior
      · exfalso
        apply e'.2
        rw [heImage]
        exact Sym2.isDiag_map_collapseSet_of_toFinset_subset e.1
          (mem_edgesInside.mp hInternal).2
      · have hMap := Sym2.map_collapseSet_eq_self_of_toFinset_subset_outside
          (r := r) e.1 (mem_edgesInside.mp hExterior).2
        have heEq : e' = e := by
          apply Subtype.ext
          exact heImage.trans hMap
        subst e'
        exact Finset.mem_union_left _ hExterior
    · obtain ⟨u, huOutside, heNew⟩ := mem_crossEdgesTo.mp hCross
      have huK : u ∉ K := (Finset.mem_sdiff.mp huOutside).2
      obtain ⟨hru, hMap⟩ :=
        exists_simpleEdge_eq_map_collapseSet_of_mem_newEdgesAt hrK huK heNew
      apply Finset.mem_union_right
      apply mem_collapsedBoundaryEdges.mpr
      refine ⟨u, huOutside, ⟨e, heNew⟩, hru, ?_⟩
      apply Subtype.ext
      exact heImage.trans hMap.symm

end RB31E2E
