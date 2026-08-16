import RB31EndToEnd.Combinatorics.Sparse22.Construction

/-!
# The `K₄` boundary of the Nixon--Owen triangle-sequence argument

The low-degree part of the Nixon--Owen reduction theorem ends with a
degree-three vertex contained in a named `K₄`.  This file isolates the
next, genuinely different, combinatorial layer.  In particular it proves
that a named `K₄` is the base graph as soon as the active graph has at most
four vertices, with no appeal to an informal graph identification.

The later declarations record the exact local overlap obstructions which
feed the triangle-sequence argument.  They deliberately retain named
vertices and edge provenance: no assertion that the full construction
theorem has already been proved is hidden in an interface hypothesis.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- The four vertices carried by a named `K₄` witness. -/
def namedK4Vertices (v a b c : V) : Finset V := {v, a, b, c}

@[simp]
theorem mem_namedK4Vertices {v a b c x : V} :
    x ∈ namedK4Vertices v a b c ↔ x = v ∨ x = a ∨ x = b ∨ x = c := by
  simp [namedK4Vertices]

theorem card_namedK4Vertices
    {F : SimpleEdgeSet V} {v a b c : V}
    (hK : NamedK4Witness F v a b c) :
    (namedK4Vertices v a b c).card = 4 := by
  simp [namedK4Vertices, hK.hva, hK.hvb, hK.hvc,
    hK.hab, hK.hac, hK.hbc]

theorem namedK4Vertices_subset
    {F : SimpleEdgeSet V} {X : Finset V} {v a b c : V}
    (hG : SimpleTight22On F X) (hK : NamedK4Witness F v a b c) :
    namedK4Vertices v a b c ⊆ X := by
  intro x hx
  rw [mem_namedK4Vertices] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hG.supported hK.va_mem (by simp)
  · exact hG.supported hK.va_mem (by simp)
  · exact hG.supported hK.vb_mem (by simp)
  · exact hG.supported hK.vc_mem (by simp)

theorem namedK4_isCliqueEdgeSet
    {F : SimpleEdgeSet V} {v a b c : V}
    (hK : NamedK4Witness F v a b c) :
    IsCliqueEdgeSet F (namedK4Vertices v a b c) := by
  intro x hx y hy hxy
  rw [mem_namedK4Vertices] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl
  all_goals try exact (hxy rfl).elim
  · exact hK.va_mem
  · exact hK.vb_mem
  · exact hK.vc_mem
  · rw [simpleEdge_comm]
    exact hK.va_mem
  · exact hK.ab_mem
  · exact hK.ac_mem
  · rw [simpleEdge_comm]
    exact hK.vb_mem
  · rw [simpleEdge_comm]
    exact hK.ab_mem
  · exact hK.bc_mem
  · rw [simpleEdge_comm]
    exact hK.vc_mem
  · rw [simpleEdge_comm]
    exact hK.ac_mem
  · rw [simpleEdge_comm]
    exact hK.bc_mem

/-- A named `K₄` occupying an active graph of cardinality at most four is
definitionally promoted to the exact `K₄` base object. -/
theorem isK4Base_of_namedK4_of_card_le_four
    {F : SimpleEdgeSet V} {X : Finset V} {v a b c : V}
    (hG : SimpleTight22On F X) (hK : NamedK4Witness F v a b c)
    (hXcard : X.card ≤ 4) :
    IsK4Base F X := by
  have hKX := namedK4Vertices_subset hG hK
  have hKcard := card_namedK4Vertices hK
  have hXeq : X = namedK4Vertices v a b c := by
    apply Finset.Subset.antisymm
    · exact Finset.eq_of_subset_of_card_le hKX (by omega) |>.symm.subset
    · exact hKX
  subst X
  exact ⟨hKcard, hG, namedK4_isCliqueEdgeSet hK⟩

/-- The existing degree-three reduction theorem, sharpened at the four-
vertex boundary: either a genuine reduction exists, the graph is exactly
`K₄`, or the certified named `K₄` lies in a graph with at least five active
vertices. -/
theorem hasNixonOwenReduction_or_isK4Base_or_large_namedK4
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨ IsK4Base F X ∨
      ∃ v ∈ X, ∃ a b c : V,
        NamedK4Witness F v a b c ∧ 5 ≤ X.card := by
  rcases hasNixonOwenReduction_or_degree_three_in_K4 hG hXcard with
      hReduce | ⟨v, hv, a, b, c, hK⟩
  · exact Or.inl hReduce
  · by_cases hFour : X.card ≤ 4
    · exact Or.inr (Or.inl (isK4Base_of_namedK4_of_card_le_four hG hK hFour))
    · exact Or.inr (Or.inr ⟨v, hv, a, b, c, hK, by omega⟩)

end RB31E2E
