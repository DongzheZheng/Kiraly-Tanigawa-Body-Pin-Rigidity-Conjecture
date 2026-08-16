import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Simple `(2,2)`-sparse edge sets

This file uses finite sets of unordered, non-diagonal vertex pairs.  Thus
parallel occurrences and loops are absent by construction.  Multiplicities
belong to the body--pin incidence layer, not to the sparse support.
-/

namespace RB31E2E

/-- An unordered edge with two distinct endpoints. -/
abbrev SimpleEdge (V : Type*) := {e : Sym2 V // ¬e.IsDiag}

/-- An occurrence-free finite simple edge set. -/
abbrev SimpleEdgeSet (V : Type*) := Finset (SimpleEdge V)

namespace SimpleEdge

variable {V : Type*} [DecidableEq V]

/-- The two endpoints of a simple edge. -/
def vertices (e : SimpleEdge V) : Finset V :=
  e.1.toFinset

@[simp]
theorem card_vertices (e : SimpleEdge V) : e.vertices.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.1 e.2

end SimpleEdge

variable {V : Type*} [DecidableEq V]

/-- Edges of `F` whose two endpoints lie in `X`. -/
def edgesInside (F : SimpleEdgeSet V) (X : Finset V) : SimpleEdgeSet V :=
  F.filter fun e => e.vertices ⊆ X

@[simp]
theorem mem_edgesInside {F : SimpleEdgeSet V} {X : Finset V} {e : SimpleEdge V} :
    e ∈ edgesInside F X ↔ e ∈ F ∧ e.vertices ⊆ X := by
  simp [edgesInside]

theorem edgesInside_subset (F : SimpleEdgeSet V) (X : Finset V) :
    edgesInside F X ⊆ F := by
  intro e he
  exact (mem_edgesInside.mp he).1

theorem edgesInside_mono_edges {F G : SimpleEdgeSet V} (hFG : F ⊆ G)
    (X : Finset V) : edgesInside F X ⊆ edgesInside G X := by
  intro e he
  exact mem_edgesInside.mpr ⟨hFG (mem_edgesInside.mp he).1, (mem_edgesInside.mp he).2⟩

theorem edgesInside_mono_vertices (F : SimpleEdgeSet V) {X Y : Finset V}
    (hXY : X ⊆ Y) : edgesInside F X ⊆ edgesInside F Y := by
  intro e he
  exact mem_edgesInside.mpr
    ⟨(mem_edgesInside.mp he).1, (mem_edgesInside.mp he).2.trans hXY⟩

theorem edgesInside_insert (F : SimpleEdgeSet V) (e : SimpleEdge V) (X : Finset V) :
    edgesInside (insert e F) X =
      if e.vertices ⊆ X then insert e (edgesInside F X) else edgesInside F X := by
  simpa only [edgesInside] using
    (Finset.filter_insert (p := fun f : SimpleEdge V => f.vertices ⊆ X) e F)

/-- Every nonempty induced vertex set obeys the `(2,2)` count. -/
def Sparse22 (F : SimpleEdgeSet V) : Prop :=
  ∀ X : Finset V, X.Nonempty → (edgesInside F X).card ≤ 2 * (X.card - 1)

/-- A nonempty vertex set on which the `(2,2)` inequality is tight. -/
def Tight22 (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  X.Nonempty ∧ (edgesInside F X).card = 2 * (X.card - 1)

@[simp]
theorem sparse22_empty : Sparse22 (∅ : SimpleEdgeSet V) := by
  intro X hX
  simp [edgesInside]

theorem Sparse22.mono {F G : SimpleEdgeSet V} (hF : Sparse22 F) (hGF : G ⊆ F) :
    Sparse22 G := by
  intro X hX
  exact (Finset.card_le_card (edgesInside_mono_edges hGF X)).trans (hF X hX)

/--
If adjoining a new simple edge destroys `(2,2)`-sparsity, some nonempty
vertex set contains both endpoints and was already tight before the edge
was adjoined.
-/
theorem exists_tight22_of_not_sparse22_insert {F : SimpleEdgeSet V} {e : SimpleEdge V}
    (hF : Sparse22 F) (heF : e ∉ F) (hbad : ¬ Sparse22 (insert e F)) :
    ∃ X : Finset V, X.Nonempty ∧ e.vertices ⊆ X ∧ Tight22 F X := by
  rw [Sparse22] at hbad
  push Not at hbad
  obtain ⟨X, hX, hviol⟩ := hbad
  have heX : e.vertices ⊆ X := by
    by_contra heX
    have hsame : edgesInside (insert e F) X = edgesInside F X := by
      simp [edgesInside_insert, heX]
    rw [hsame] at hviol
    exact (Nat.not_lt_of_ge (hF X hX)) hviol
  have heInside : e ∉ edgesInside F X := by
    simpa only [mem_edgesInside, not_and_or] using Or.inl heF
  have hcard :
      (edgesInside (insert e F) X).card = (edgesInside F X).card + 1 := by
    simp [edgesInside_insert, heX, heInside]
  have htight : (edgesInside F X).card = 2 * (X.card - 1) := by
    have hle := hF X hX
    rw [hcard] at hviol
    omega
  exact ⟨X, hX, heX, hX, htight⟩

end RB31E2E
