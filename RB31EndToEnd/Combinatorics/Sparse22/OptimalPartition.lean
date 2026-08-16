import RB31EndToEnd.Combinatorics.Sparse22.Uncrossing
import Mathlib.Order.Partition.Finpartition

/-!
# Optimal tight-block partitions for `(2,2)`-sparse sets

The construction is canonical after a maximum-cardinality sparse subset
`F` is fixed: the block of a vertex is the union of all `F`-tight sets
containing that vertex.  No choice of a maximal tight set is made.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- `F` is a maximum-cardinality `(2,2)`-sparse subset of `J`. -/
structure IsMaximumSparseSubedge (J F : SimpleEdgeSet V) : Prop where
  subset : F ⊆ J
  sparse : Sparse22 F
  card_max : ∀ {G : SimpleEdgeSet V}, G ⊆ J → Sparse22 G → G.card ≤ F.card

/-- All sparse subsets of a fixed finite simple edge set. -/
noncomputable def sparseSubsets (J : SimpleEdgeSet V) : Finset (SimpleEdgeSet V) := by
  classical
  exact J.powerset.filter Sparse22

theorem mem_sparseSubsets {J F : SimpleEdgeSet V} :
    F ∈ sparseSubsets J ↔ F ⊆ J ∧ Sparse22 F := by
  classical
  simp [sparseSubsets]

/-- Every finite simple edge set has a maximum-cardinality sparse subset. -/
theorem exists_isMaximumSparseSubedge (J : SimpleEdgeSet V) :
    ∃ F : SimpleEdgeSet V, IsMaximumSparseSubedge J F := by
  classical
  have hne : (sparseSubsets J).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [mem_sparseSubsets]
  obtain ⟨F, hFmem, hFmax⟩ :=
    Finset.exists_max_image (sparseSubsets J) Finset.card hne
  have hF := mem_sparseSubsets.mp hFmem
  refine ⟨F, hF.1, hF.2, ?_⟩
  intro G hGJ hGsparse
  exact hFmax G (mem_sparseSubsets.mpr ⟨hGJ, hGsparse⟩)

theorem IsMaximumSparseSubedge.not_sparse_insert
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    ¬ Sparse22 (insert e F) := by
  intro hinsSparse
  have hinsJ : insert e F ⊆ J := Finset.insert_subset heJ hF.subset
  have hcard := hF.card_max hinsJ hinsSparse
  rw [Finset.card_insert_of_notMem heF] at hcard
  omega

/-- Every edge omitted by a maximum sparse subset has an `F`-tight witness. -/
theorem IsMaximumSparseSubedge.missing_edge_tight
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    ∃ X : Finset V, X.Nonempty ∧ e.vertices ⊆ X ∧ Tight22 F X :=
  exists_tight22_of_not_sparse22_insert hF.sparse heF
    (hF.not_sparse_insert heJ heF)

theorem SimpleEdge.not_vertices_subset_singleton (e : SimpleEdge V) (v : V) :
    ¬ e.vertices ⊆ {v} := by
  intro hev
  have hcard := Finset.card_le_card hev
  rw [e.card_vertices] at hcard
  simp at hcard

/-- Every singleton vertex set is tight; looplessness is used here. -/
theorem tight22_singleton (F : SimpleEdgeSet V) (v : V) : Tight22 F {v} := by
  have hempty : edgesInside F {v} = ∅ := by
    ext e
    simp [e.not_vertices_subset_singleton v]
  constructor
  · simp
  · simp [hempty]

/-- A finite family of tight sets with a common vertex has tight union. -/
theorem tight22_biUnion_of_common_vertex {F : SimpleEdgeSet V} (hF : Sparse22 F)
    {A : Finset (Finset V)} (hA : A.Nonempty) {v : V}
    (hv : ∀ X ∈ A, v ∈ X) (ht : ∀ X ∈ A, Tight22 F X) :
    Tight22 F (A.biUnion id) := by
  revert hv ht
  induction hA using Finset.Nonempty.cons_induction with
  | singleton X =>
      intro hv ht
      simpa using ht X (by simp)
  | cons X A hXA hA ih =>
      intro hv ht
      have htX : Tight22 F X := ht X (by simp)
      have htA : Tight22 F (A.biUnion id) := by
        apply ih
        · intro Y hY
          exact hv Y (by simp [hY])
        · intro Y hY
          exact ht Y (by simp [hY])
      have hinter : (X ∩ A.biUnion id).Nonempty := by
        obtain ⟨Y, hYA⟩ := hA
        refine ⟨v, ?_⟩
        exact Finset.mem_inter.mpr
          ⟨hv X (by simp), Finset.mem_biUnion.mpr ⟨Y, hYA, hv Y (by simp [hYA])⟩⟩
      have hu := (tight22_union_inter hF htX htA hinter).1
      simpa using hu

variable [Fintype V]

/-- All tight vertex sets containing `v`. -/
noncomputable def tightFamily (F : SimpleEdgeSet V) (v : V) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun X => v ∈ X ∧ Tight22 F X

@[simp]
theorem mem_tightFamily {F : SimpleEdgeSet V} {v : V} {X : Finset V} :
    X ∈ tightFamily F v ↔ v ∈ X ∧ Tight22 F X := by
  classical
  simp [tightFamily]

theorem tightFamily_nonempty (F : SimpleEdgeSet V) (v : V) :
    (tightFamily F v).Nonempty := by
  classical
  refine ⟨{v}, ?_⟩
  simp [tight22_singleton]

/-- The union of every tight set containing `v`. -/
noncomputable def tightHull (F : SimpleEdgeSet V) (v : V) : Finset V :=
  (tightFamily F v).biUnion id

theorem tightHull_tight {F : SimpleEdgeSet V} (hF : Sparse22 F) (v : V) :
    Tight22 F (tightHull F v) := by
  apply tight22_biUnion_of_common_vertex hF (tightFamily_nonempty F v)
  · intro X hX
    exact (mem_tightFamily.mp hX).1
  · intro X hX
    exact (mem_tightFamily.mp hX).2

@[simp]
theorem mem_tightHull_iff {F : SimpleEdgeSet V} {v w : V} :
    w ∈ tightHull F v ↔
      ∃ X : Finset V, Tight22 F X ∧ v ∈ X ∧ w ∈ X := by
  simp only [tightHull, Finset.mem_biUnion, mem_tightFamily, id_eq]
  aesop

@[simp]
theorem mem_tightHull_self (F : SimpleEdgeSet V) (v : V) : v ∈ tightHull F v := by
  rw [mem_tightHull_iff]
  exact ⟨{v}, tight22_singleton F v, by simp⟩

theorem mem_tightHull_comm {F : SimpleEdgeSet V} {v w : V} :
    w ∈ tightHull F v ↔ v ∈ tightHull F w := by
  simp only [mem_tightHull_iff]
  constructor <;> rintro ⟨X, hX, hv, hw⟩ <;> exact ⟨X, hX, hw, hv⟩

theorem tight_subset_tightHull {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hX : Tight22 F X) (hv : v ∈ X) : X ⊆ tightHull F v := by
  intro w hw
  rw [mem_tightHull_iff]
  exact ⟨X, hX, hv, hw⟩

theorem tightHull_eq_of_mem {F : SimpleEdgeSet V} (hF : Sparse22 F) {v w : V}
    (hw : w ∈ tightHull F v) : tightHull F w = tightHull F v := by
  apply Finset.Subset.antisymm
  · apply tight_subset_tightHull (tightHull_tight hF w)
    exact mem_tightHull_comm.mp hw
  · exact tight_subset_tightHull (tightHull_tight hF v) hw

/-- Vertices are equivalent when they lie in one common tight set. -/
noncomputable def tightSetoid (F : SimpleEdgeSet V) (hF : Sparse22 F) : Setoid V where
  r v w := w ∈ tightHull F v
  iseqv := {
    refl := mem_tightHull_self F
    symm := fun hvw => mem_tightHull_comm.mp hvw
    trans := fun hvw hwz => by
      rw [tightHull_eq_of_mem hF hvw] at hwz
      exact hwz }

/-- The canonical partition into maximal tight blocks. -/
noncomputable def tightPartition (F : SimpleEdgeSet V) (hF : Sparse22 F) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid (tightSetoid F hF)

theorem tightPartition_part_eq_tightHull {F : SimpleEdgeSet V} (hF : Sparse22 F) (v : V) :
    (tightPartition F hF).part v = tightHull F v := by
  classical
  ext w
  simp [tightPartition, tightSetoid, Finpartition.mem_part_ofSetoid_iff_rel]

/-- Every part of the canonical partition is tight. -/
theorem tight_of_mem_tightPartition {F : SimpleEdgeSet V} (hF : Sparse22 F)
    {X : Finset V} (hX : X ∈ (tightPartition F hF).parts) : Tight22 F X := by
  obtain ⟨v, hv⟩ := (tightPartition F hF).nonempty_of_mem_parts hX
  have hpart : (tightPartition F hF).part v = X :=
    (tightPartition F hF).part_eq_of_mem hX hv
  rw [← hpart, tightPartition_part_eq_tightHull]
  exact tightHull_tight hF v

/-- An edge is internal when all its endpoints lie in one partition block. -/
def InternalTo (P : Finpartition (Finset.univ : Finset V)) (e : SimpleEdge V) : Prop :=
  ∃ X ∈ P.parts, e.vertices ⊆ X

/-- Every edge omitted by a maximum sparse set is internal to its tight partition. -/
theorem IsMaximumSparseSubedge.internal_missing_edge
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    InternalTo (tightPartition F hF.sparse) e := by
  obtain ⟨X, hXne, heX, hXtight⟩ := hF.missing_edge_tight heJ heF
  obtain ⟨v, hvX⟩ := hXne
  refine ⟨(tightPartition F hF.sparse).part v, ?_, ?_⟩
  · exact (tightPartition F hF.sparse).part_mem.mpr (by simp)
  · rw [tightPartition_part_eq_tightHull]
    exact heX.trans (tight_subset_tightHull hXtight hvX)

/-- Edges lying inside some block of `P`. -/
noncomputable def internalEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleEdgeSet V := by
  classical
  exact K.filter (InternalTo P)

/-- Edges crossing the blocks of `P`. -/
noncomputable def crossEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleEdgeSet V := by
  classical
  exact K.filter fun e => ¬ InternalTo P e

@[simp]
theorem mem_internalEdges {K : SimpleEdgeSet V}
    {P : Finpartition (Finset.univ : Finset V)} {e : SimpleEdge V} :
    e ∈ internalEdges K P ↔ e ∈ K ∧ InternalTo P e := by
  classical
  simp [internalEdges]

@[simp]
theorem mem_crossEdges {K : SimpleEdgeSet V}
    {P : Finpartition (Finset.univ : Finset V)} {e : SimpleEdge V} :
    e ∈ crossEdges K P ↔ e ∈ K ∧ ¬ InternalTo P e := by
  classical
  simp [crossEdges]

theorem card_internalEdges_add_card_crossEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (internalEdges K P).card + (crossEdges K P).card = K.card := by
  classical
  exact Finset.card_filter_add_card_filter_not (s := K) (InternalTo P)

theorem internalEdges_eq_biUnion (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    internalEdges K P = P.parts.biUnion (edgesInside K) := by
  classical
  ext e
  simp only [mem_internalEdges, InternalTo, Finset.mem_biUnion, mem_edgesInside]
  aesop

theorem pairwiseDisjoint_edgesInside (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (P.parts : Set (Finset V)).PairwiseDisjoint (edgesInside K) := by
  intro A hA B hB hAB
  rw [Function.onFun, Finset.disjoint_left]
  intro e heA heB
  have hverts : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
  obtain ⟨v, hv⟩ := hverts
  exact (Finset.disjoint_left.mp (P.disjoint hA hB hAB))
    ((mem_edgesInside.mp heA).2 hv) ((mem_edgesInside.mp heB).2 hv)

theorem card_internalEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (internalEdges K P).card = ∑ X ∈ P.parts, (edgesInside K X).card := by
  classical
  rw [internalEdges_eq_biUnion, Finset.card_biUnion (pairwiseDisjoint_edgesInside K P)]

theorem sum_two_card_sub_one_parts
    (P : Finpartition (Finset.univ : Finset V)) :
    (∑ X ∈ P.parts, 2 * (X.card - 1)) =
      2 * (Fintype.card V - P.parts.card) := by
  have hsub :
      (∑ X ∈ P.parts, (X.card - 1)) =
        (∑ X ∈ P.parts, X.card) - P.parts.card := by
    calc
      (∑ X ∈ P.parts, (X.card - 1)) =
          (∑ X ∈ P.parts, X.card) - (∑ _X ∈ P.parts, 1) := by
        apply Finset.sum_tsub_distrib
        intro X hX
        exact Finset.card_pos.mpr (P.nonempty_of_mem_parts hX)
      _ = (∑ X ∈ P.parts, X.card) - P.parts.card := by simp
  calc
    (∑ X ∈ P.parts, 2 * (X.card - 1)) =
        2 * (∑ X ∈ P.parts, (X.card - 1)) := by
      symm
      exact Finset.mul_sum P.parts (fun X => X.card - 1) 2
    _ = 2 * ((∑ X ∈ P.parts, X.card) - P.parts.card) := by rw [hsub]
    _ = 2 * (Fintype.card V - P.parts.card) := by
      rw [P.sum_card_parts]
      simp

/-- The partition expression associated with a simple support. -/
noncomputable def sparsePartitionTerm (J : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : ℕ :=
  2 * (Fintype.card V - P.parts.card) + (crossEdges J P).card

theorem crossEdges_mono {K L : SimpleEdgeSet V} (hKL : K ⊆ L)
    (P : Finpartition (Finset.univ : Finset V)) : crossEdges K P ⊆ crossEdges L P := by
  intro e he
  exact mem_crossEdges.mpr ⟨hKL (mem_crossEdges.mp he).1, (mem_crossEdges.mp he).2⟩

theorem IsMaximumSparseSubedge.crossEdges_eq
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F) :
    crossEdges F (tightPartition F hF.sparse) =
      crossEdges J (tightPartition F hF.sparse) := by
  classical
  ext e
  simp only [mem_crossEdges]
  constructor
  · rintro ⟨heF, heCross⟩
    exact ⟨hF.subset heF, heCross⟩
  · rintro ⟨heJ, heCross⟩
    refine ⟨?_, heCross⟩
    by_contra heFmem
    exact heCross (hF.internal_missing_edge heJ heFmem)

theorem card_internalEdges_tightPartition {F : SimpleEdgeSet V} (hF : Sparse22 F) :
    (internalEdges F (tightPartition F hF)).card =
      2 * (Fintype.card V - (tightPartition F hF).parts.card) := by
  rw [card_internalEdges]
  calc
    (∑ X ∈ (tightPartition F hF).parts, (edgesInside F X).card) =
        ∑ X ∈ (tightPartition F hF).parts, 2 * (X.card - 1) := by
      apply Finset.sum_congr rfl
      intro X hX
      exact (tight_of_mem_tightPartition hF hX).2
    _ = 2 * (Fintype.card V - (tightPartition F hF).parts.card) :=
      sum_two_card_sub_one_parts (tightPartition F hF)

/--
The canonical tight partition realizes equality in the partition bound for
a maximum sparse subset.
-/
theorem IsMaximumSparseSubedge.card_eq_sparsePartitionTerm
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F) :
    F.card = sparsePartitionTerm J (tightPartition F hF.sparse) := by
  have hsplit :=
    card_internalEdges_add_card_crossEdges F (tightPartition F hF.sparse)
  rw [card_internalEdges_tightPartition hF.sparse, hF.crossEdges_eq] at hsplit
  exact hsplit.symm

/-- Every sparse subset is bounded by every partition term. -/
theorem Sparse22.card_le_sparsePartitionTerm
    {J F : SimpleEdgeSet V} (hF : Sparse22 F) (hFJ : F ⊆ J)
    (P : Finpartition (Finset.univ : Finset V)) :
    F.card ≤ sparsePartitionTerm J P := by
  have hInternal :
      (internalEdges F P).card ≤ 2 * (Fintype.card V - P.parts.card) := by
    rw [card_internalEdges]
    calc
      (∑ X ∈ P.parts, (edgesInside F X).card) ≤
          ∑ X ∈ P.parts, 2 * (X.card - 1) := by
        apply Finset.sum_le_sum
        intro X hX
        exact hF X (P.nonempty_of_mem_parts hX)
      _ = 2 * (Fintype.card V - P.parts.card) := sum_two_card_sub_one_parts P
  have hCross : (crossEdges F P).card ≤ (crossEdges J P).card :=
    Finset.card_le_card (crossEdges_mono hFJ P)
  have hsplit := card_internalEdges_add_card_crossEdges F P
  simp only [sparsePartitionTerm]
  omega

/--
If every partition term is at least `R`, then `J` has an `R`-edge
`(2,2)`-sparse subset.  This is the extraction statement needed by the
body--pin bridge and does not invoke a graphic-matroid-union API.
-/
theorem exists_sparse22_of_all_partition_terms (J : SimpleEdgeSet V) (R : ℕ)
    (hR : ∀ P : Finpartition (Finset.univ : Finset V), R ≤ sparsePartitionTerm J P) :
    ∃ F : SimpleEdgeSet V, F ⊆ J ∧ Sparse22 F ∧ F.card = R := by
  obtain ⟨M, hM⟩ := exists_isMaximumSparseSubedge J
  have hRM : R ≤ M.card := by
    rw [hM.card_eq_sparsePartitionTerm]
    exact hR (tightPartition M hM.sparse)
  obtain ⟨F, hFM, hFcard⟩ := Finset.exists_subset_card_eq hRM
  exact ⟨F, hFM.trans hM.subset, hM.sparse.mono hFM, hFcard⟩

end RB31E2E
