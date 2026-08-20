import RB31EndToEnd.API.Sparse22

/-! A consumer of the public `(2,2)`-sparsity facade and no other project facade. -/

namespace PublicAPISmoke.Sparse22

universe u

def expandedSimpleEdge (V : Type u) : Type u :=
  {e : Sym2 V // ¬ e.IsDiag}

example (V : Type u) :
    RB31E2E.SimpleEdge V = expandedSimpleEdge V :=
  rfl

example (V : Type u) :
    expandedSimpleEdge V = RB31E2E.SimpleEdge V :=
  rfl

def expandedSimpleEdgeSet (V : Type u) : Type u :=
  Finset (RB31E2E.SimpleEdge V)

example (V : Type u) :
    RB31E2E.SimpleEdgeSet V = expandedSimpleEdgeSet V :=
  rfl

example (V : Type u) :
    expandedSimpleEdgeSet V = RB31E2E.SimpleEdgeSet V :=
  rfl

def edgeCarrier (V : Type u) : Type u :=
  RB31E2E.SimpleEdge V

def edgeVertices {V : Type*} [DecidableEq V]
    (e : RB31E2E.SimpleEdge V) : Finset V :=
  e.vertices

def inducedEdges {V : Type*} [DecidableEq V]
    (F : RB31E2E.SimpleEdgeSet V) (X : Finset V) :
    RB31E2E.SimpleEdgeSet V :=
  RB31E2E.edgesInside F X

def isTight {V : Type*} [DecidableEq V]
    (F : RB31E2E.SimpleEdgeSet V) (X : Finset V) : Prop :=
  RB31E2E.Tight22 F X

example {V : Type*} [DecidableEq V] :
    RB31E2E.Sparse22 (∅ : RB31E2E.SimpleEdgeSet V) :=
  RB31E2E.sparse22_empty

example {V : Type*} [DecidableEq V]
    {F : RB31E2E.SimpleEdgeSet V} {A B : Finset V}
    (hF : RB31E2E.Sparse22 F)
    (hA : RB31E2E.Tight22 F A)
    (hB : RB31E2E.Tight22 F B)
    (hAB : (A ∩ B).Nonempty) :
    RB31E2E.Tight22 F (A ∪ B) ∧
      RB31E2E.Tight22 F (A ∩ B) :=
  RB31E2E.tight22_union_inter hF hA hB hAB

noncomputable def sparsePartitionTerm
    {V : Type*} [DecidableEq V] [Fintype V]
    (J : RB31E2E.SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : ℕ :=
  RB31E2E.sparsePartitionTerm J P

example {V : Type*} [DecidableEq V] [Fintype V]
    (J : RB31E2E.SimpleEdgeSet V) (R : ℕ)
    (hR : ∀ P : Finpartition (Finset.univ : Finset V),
      R ≤ RB31E2E.sparsePartitionTerm J P) :
    ∃ F : RB31E2E.SimpleEdgeSet V,
      F ⊆ J ∧ RB31E2E.Sparse22 F ∧ F.card = R :=
  RB31E2E.exists_sparse22_of_all_partition_terms J R hR

example {V : Type*} [DecidableEq V] [Fintype V]
    (F : RB31E2E.SimpleEdgeSet V) (hF : RB31E2E.Sparse22 F)
    (hcard : 4 ≤ Fintype.card V) :
    ∃ G : RB31E2E.SimpleEdgeSet V,
      F ⊆ G ∧ RB31E2E.Sparse22 G ∧
        RB31E2E.Tight22 G (Finset.univ : Finset V) :=
  RB31E2E.exists_tight22_completion F hF hcard

noncomputable def mapSimpleEdge
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (e : RB31E2E.SimpleEdge V) :
    RB31E2E.SimpleEdge W :=
  RB31E2E.Sparse22Transport.mapSimpleEdge f e

noncomputable def mapEdgeSet
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (F : RB31E2E.SimpleEdgeSet V) :
    RB31E2E.SimpleEdgeSet W :=
  RB31E2E.Sparse22Transport.mapEdgeSet f F

example {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) {F : RB31E2E.SimpleEdgeSet V}
    {H : RB31E2E.SimpleEdgeSet W}
    (hH : RB31E2E.Sparse22 H)
    (hFH : RB31E2E.Sparse22Transport.mapEdgeSet f F ⊆ H) :
    RB31E2E.Sparse22 F :=
  RB31E2E.Sparse22Transport.sparse22_of_mapEdgeSet_subset f hH hFH

end PublicAPISmoke.Sparse22
