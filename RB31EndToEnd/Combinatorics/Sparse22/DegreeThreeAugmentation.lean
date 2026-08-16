import RB31EndToEnd.Combinatorics.Sparse22.Construction

/-!
# Adding a missing neighbour edge at a sparse degree-three vertex

The inverse-Henneberg lemmas in `Construction` package their conclusion as
a reduction of a *tight* graph.  Provenance-flag induction needs the local
fact before any tight completion: in an arbitrary sparse graph, if the
three neighbours of a degree-three vertex do not span a triangle, at least
one missing neighbour edge is sparse after deleting the vertex.

The proof is a tight-set obstruction and uncrossing argument that does not
require global tightness or a chosen completion.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- If exactly the pair `ab` is missing among the three neighbour pairs,
then it can be inserted after deleting the degree-three vertex. -/
theorem sparse22_insert_missing_neighbor_edge_of_other_two
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hacF : simpleEdge a c hac ∈ F)
    (hbcF : simpleEdge b c hbc ∈ F) :
    Sparse22
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) := by
  by_contra hBad
  have hSparseDelete : Sparse22 (deleteVertexEdges F v) :=
    hSparse.mono (deleteVertexEdges_subset F v)
  obtain ⟨Y, hYne, haY, hbY, hvY, hYtight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hva hab hSparseDelete habF hBad
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hcY : c ∉ Y := by
    intro hcY
    have hIncidentSupported :
        SupportedOn (incidentEdges F v) (insert v Y) := by
      intro e he
      rw [hIncidentEq] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · rw [vertices_simpleEdge]
        simp [haY]
      · rw [vertices_simpleEdge]
        simp [hbY]
      · rw [vertices_simpleEdge]
        simp [hcY]
    have hCard := card_edgesInside_insert_eq_degree_add
      F Y v hvY hIncidentSupported
    have hSparseZ := hSparse (insert v Y) ⟨v, by simp⟩
    have hZcard : (insert v Y).card = Y.card + 1 := by
      rw [Finset.card_insert_of_notMem hvY]
    rw [hCard, hDegree, hYtight.2, hZcard] at hSparseZ
    have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
    omega
  let eac : SimpleEdge V := simpleEdge a c hac
  let ebc : SimpleEdge V := simpleEdge b c hbc
  let R : SimpleEdgeSet V := deleteVertexEdges F v
  have eacR : eac ∈ R := by
    rw [mem_deleteVertexEdges]
    refine ⟨hacF, ?_⟩
    rw [vertices_simpleEdge]
    simp [hva, hvc]
  have ebcR : ebc ∈ R := by
    rw [mem_deleteVertexEdges]
    refine ⟨hbcF, ?_⟩
    rw [vertices_simpleEdge]
    simp [hvb, hvc]
  have eacNew : eac ∈ edgesInside R (insert c Y) := by
    rw [mem_edgesInside]
    refine ⟨eacR, ?_⟩
    rw [vertices_simpleEdge]
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_insert_of_mem haY
    · exact Finset.mem_insert_self _ _
  have ebcNew : ebc ∈ edgesInside R (insert c Y) := by
    rw [mem_edgesInside]
    refine ⟨ebcR, ?_⟩
    rw [vertices_simpleEdge]
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_insert_of_mem hbY
    · exact Finset.mem_insert_self _ _
  have hPairCard : ({eac, ebc} : SimpleEdgeSet V).card = 2 := by
    simp [eac, ebc, hab, hac]
  have hPairDisjoint :
      Disjoint (edgesInside R Y) ({eac, ebc} : SimpleEdgeSet V) := by
    rw [Finset.disjoint_left]
    intro e heOld hePair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
    rcases hePair with rfl | rfl
    · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [eac]))
    · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [ebc]))
  have hUnionSubset :
      edgesInside R Y ∪ ({eac, ebc} : SimpleEdgeSet V) ⊆
        edgesInside R (insert c Y) := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heOld | hePair
    · exact edgesInside_mono_vertices R (Finset.subset_insert c Y) heOld
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
      rcases hePair with rfl | rfl
      · exact eacNew
      · exact ebcNew
  have hDeletedLower :
      (edgesInside R Y).card + 2 ≤
        (edgesInside R (insert c Y)).card := by
    rw [← hPairCard, ← Finset.card_union_of_disjoint hPairDisjoint]
    exact Finset.card_le_card hUnionSubset
  have hvInsertCY : v ∉ insert c Y := by
    simp [hvc, hvY]
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (insert c Y)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haY]
    · rw [vertices_simpleEdge]
      simp [hbY]
    · rw [vertices_simpleEdge]
      simp
  have hCard := card_edgesInside_insert_eq_degree_add
    F (insert c Y) v hvInsertCY hIncidentSupported
  have hSparseZ := hSparse (insert v (insert c Y)) ⟨v, by simp⟩
  have hCYcard : (insert c Y).card = Y.card + 1 := by
    rw [Finset.card_insert_of_notMem hcY]
  have hZcard : (insert v (insert c Y)).card = Y.card + 2 := by
    rw [Finset.card_insert_of_notMem hvInsertCY, hCYcard]
  rw [hCard, hDegree, hZcard] at hSparseZ
  dsimp [R] at hDeletedLower
  rw [hYtight.2] at hDeletedLower
  have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
  omega

/-- If two neighbour pairs are missing, at least one of the two can be
inserted after deleting the degree-three vertex. -/
theorem sparse22_insert_one_of_two_missing_neighbor_edges
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hbcF : simpleEdge b c hbc ∉ F) :
    Sparse22
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) ∨
      Sparse22
        (insert (simpleEdge b c hbc) (deleteVertexEdges F v)) := by
  have hSparseR : Sparse22 (deleteVertexEdges F v) :=
    hSparse.mono (deleteVertexEdges_subset F v)
  by_cases hAB :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))
  · exact Or.inl hAB
  by_cases hBC :
      Sparse22 (insert (simpleEdge b c hbc) (deleteVertexEdges F v))
  · exact Or.inr hBC
  obtain ⟨Yab, _hYabNe, haYab, hbYab, hvYab, hYabTight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hva hab hSparseR habF hAB
  obtain ⟨Ybc, _hYbcNe, hbYbc, hcYbc, hvYbc, hYbcTight⟩ :=
    exists_tight22_obstruction_of_not_hennebergTwo_admissible
      hvb hbc hSparseR hbcF hBC
  have hInterNonempty : (Yab ∩ Ybc).Nonempty :=
    ⟨b, Finset.mem_inter.mpr ⟨hbYab, hbYbc⟩⟩
  have hUnionTight : Tight22 (deleteVertexEdges F v) (Yab ∪ Ybc) :=
    (tight22_union_inter hSparseR hYabTight hYbcTight hInterNonempty).1
  have hvUnion : v ∉ Yab ∪ Ybc := by
    simp [hvYab, hvYbc]
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (Yab ∪ Ybc)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haYab]
    · rw [vertices_simpleEdge]
      simp [hbYab]
    · rw [vertices_simpleEdge]
      simp [hcYbc]
  have hCard := card_edgesInside_insert_eq_degree_add
    F (Yab ∪ Ybc) v hvUnion hIncidentSupported
  have hSparseZ := hSparse (insert v (Yab ∪ Ybc)) ⟨v, by simp⟩
  have hZcard :
      (insert v (Yab ∪ Ybc)).card = (Yab ∪ Ybc).card + 1 := by
    rw [Finset.card_insert_of_notMem hvUnion]
  rw [hCard, hDegree, hZcard, hUnionTight.2] at hSparseZ
  have hUnionPos : 0 < (Yab ∪ Ybc).card :=
    Finset.card_pos.mpr hUnionTight.1
  omega

/-- Complete local dichotomy for three named neighbours in an arbitrary
sparse graph: they already span their full triangle, or an actually absent
neighbour edge can be inserted after deleting the degree-three vertex. -/
theorem degree_three_neighbour_triangle_complete_or_addable
    {F : SimpleEdgeSet V} {v a b c : V}
    (hSparse : Sparse22 F)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    (simpleEdge a b hab ∈ F ∧ simpleEdge a c hac ∈ F ∧
        simpleEdge b c hbc ∈ F) ∨
      ∃ e : SimpleEdge V,
        e ∈ ({simpleEdge a b hab, simpleEdge a c hac,
            simpleEdge b c hbc} : SimpleEdgeSet V) ∧
        e ∉ F ∧ Sparse22 (insert e (deleteVertexEdges F v)) := by
  by_cases hAB : simpleEdge a b hab ∈ F
  · by_cases hAC : simpleEdge a c hac ∈ F
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · exact Or.inl ⟨hAB, hAC, hBC⟩
      · right
        refine ⟨simpleEdge b c hbc, by simp, hBC, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hvb hvc hva hbc (Ne.symm hab) (Ne.symm hac)
          hDegree hvbF hvcF hvaF hBC
          (by rw [← simpleEdge_comm a b hab]; exact hAB)
          (by rw [← simpleEdge_comm a c hac]; exact hAC)
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · right
        refine ⟨simpleEdge a c hac, by simp, hAC, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hva hvc hvb hac hab (Ne.symm hbc)
          hDegree hvaF hvcF hvbF hAC hAB
          (by rw [← simpleEdge_comm b c hbc]; exact hBC)
      · rcases sparse22_insert_one_of_two_missing_neighbor_edges
          hSparse hva hvc hvb hac hab (Ne.symm hbc)
          hDegree hvaF hvcF hvbF hAC
          (by rw [← simpleEdge_comm b c hbc]; exact hBC) with
          hAddAC | hAddCB
        · exact Or.inr ⟨simpleEdge a c hac, by simp, hAC, hAddAC⟩
        · refine Or.inr ⟨simpleEdge b c hbc, by simp, hBC, ?_⟩
          rw [simpleEdge_comm c b (Ne.symm hbc)] at hAddCB
          exact hAddCB
  · by_cases hBC : simpleEdge b c hbc ∈ F
    · by_cases hAC : simpleEdge a c hac ∈ F
      · right
        refine ⟨simpleEdge a b hab, by simp, hAB, ?_⟩
        exact sparse22_insert_missing_neighbor_edge_of_other_two
          hSparse hva hvb hvc hab hac hbc
          hDegree hvaF hvbF hvcF hAB hAC hBC
      · rcases sparse22_insert_one_of_two_missing_neighbor_edges
          hSparse hvb hva hvc (Ne.symm hab) hbc hac
          hDegree hvbF hvaF hvcF
          (by rw [simpleEdge_comm b a (Ne.symm hab)]; exact hAB)
          hAC with hAddBA | hAddAC
        · refine Or.inr ⟨simpleEdge a b hab, by simp, hAB, ?_⟩
          rw [simpleEdge_comm b a (Ne.symm hab)] at hAddBA
          exact hAddBA
        · exact Or.inr ⟨simpleEdge a c hac, by simp, hAC, hAddAC⟩
    · rcases sparse22_insert_one_of_two_missing_neighbor_edges
        hSparse hva hvb hvc hab hac hbc
        hDegree hvaF hvbF hvcF hAB hBC with hAddAB | hAddBC
      · exact Or.inr ⟨simpleEdge a b hab, by simp, hAB, hAddAB⟩
      · exact Or.inr ⟨simpleEdge b c hbc, by simp, hBC, hAddBC⟩

end RB31E2E
