import RB31EndToEnd.Combinatorics.Sparse22.Basic

/-!
# Tight-set uncrossing for `(2,2)`-sparsity

The intersection is required to be nonempty.  This includes the
single-vertex-intersection case; no stronger overlap assumption is needed.
For disjoint tight sets neither tightness of their union nor tightness of
their empty intersection follows in general.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

theorem edgesInside_inter (F : SimpleEdgeSet V) (A B : Finset V) :
    edgesInside F (A ∩ B) = edgesInside F A ∩ edgesInside F B := by
  ext e
  simp only [mem_edgesInside, Finset.mem_inter]
  constructor
  · rintro ⟨heF, heAB⟩
    exact ⟨⟨heF, heAB.trans Finset.inter_subset_left⟩,
      ⟨heF, heAB.trans Finset.inter_subset_right⟩⟩
  · rintro ⟨⟨heF, heA⟩, -, heB⟩
    exact ⟨heF, Finset.subset_inter heA heB⟩

theorem union_edgesInside_subset (F : SimpleEdgeSet V) (A B : Finset V) :
    edgesInside F A ∪ edgesInside F B ⊆ edgesInside F (A ∪ B) := by
  intro e he
  rcases Finset.mem_union.mp he with heA | heB
  · exact mem_edgesInside.mpr
      ⟨(mem_edgesInside.mp heA).1,
        (mem_edgesInside.mp heA).2.trans Finset.subset_union_left⟩
  · exact mem_edgesInside.mpr
      ⟨(mem_edgesInside.mp heB).1,
        (mem_edgesInside.mp heB).2.trans Finset.subset_union_right⟩

/-- Induced-edge count is supermodular on vertex sets. -/
theorem card_edgesInside_supermodular (F : SimpleEdgeSet V) (A B : Finset V) :
    (edgesInside F A).card + (edgesInside F B).card ≤
      (edgesInside F (A ∪ B)).card + (edgesInside F (A ∩ B)).card := by
  calc
    (edgesInside F A).card + (edgesInside F B).card =
        (edgesInside F A ∪ edgesInside F B).card +
          (edgesInside F A ∩ edgesInside F B).card :=
      (Finset.card_union_add_card_inter _ _).symm
    _ ≤ (edgesInside F (A ∪ B)).card +
          (edgesInside F A ∩ edgesInside F B).card :=
      Nat.add_le_add_right
        (Finset.card_le_card (union_edgesInside_subset F A B)) _
    _ = (edgesInside F (A ∪ B)).card +
          (edgesInside F (A ∩ B)).card := by
      rw [edgesInside_inter]

/--
Two tight sets with nonempty intersection uncross: both their union and
their intersection are tight.  A one-vertex intersection is allowed.
-/
theorem tight22_union_inter {F : SimpleEdgeSet V} {A B : Finset V}
    (hF : Sparse22 F) (hA : Tight22 F A) (hB : Tight22 F B)
    (hAB : (A ∩ B).Nonempty) :
    Tight22 F (A ∪ B) ∧ Tight22 F (A ∩ B) := by
  have hAunionB : (A ∪ B).Nonempty := hA.1.mono Finset.subset_union_left
  have hSuper := card_edgesInside_supermodular F A B
  have hUnionUpper := hF (A ∪ B) hAunionB
  have hInterUpper := hF (A ∩ B) hAB
  have hCardIdentity := Finset.card_union_add_card_inter A B
  have hApos : 0 < A.card := Finset.card_pos.mpr hA.1
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB.1
  have hUnionPos : 0 < (A ∪ B).card := Finset.card_pos.mpr hAunionB
  have hInterPos : 0 < (A ∩ B).card := Finset.card_pos.mpr hAB
  have hBudgetIdentity :
      2 * (A.card - 1) + 2 * (B.card - 1) =
        2 * ((A ∪ B).card - 1) + 2 * ((A ∩ B).card - 1) := by
    omega
  have hBudgetLower :
      2 * ((A ∪ B).card - 1) + 2 * ((A ∩ B).card - 1) ≤
        (edgesInside F (A ∪ B)).card + (edgesInside F (A ∩ B)).card := by
    rw [← hBudgetIdentity, ← hA.2, ← hB.2]
    exact hSuper
  have hUnionTight :
      (edgesInside F (A ∪ B)).card = 2 * ((A ∪ B).card - 1) := by
    omega
  have hInterTight :
      (edgesInside F (A ∩ B)).card = 2 * ((A ∩ B).card - 1) := by
    omega
  exact ⟨⟨hAunionB, hUnionTight⟩, ⟨hAB, hInterTight⟩⟩

end RB31E2E
