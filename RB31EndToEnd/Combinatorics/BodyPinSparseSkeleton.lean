import RB31EndToEnd.Combinatorics.BodyPinFinpartition
import RB31EndToEnd.Combinatorics.Sparse22.OptimalPartition

/-!
# A sparse null skeleton from body--pin partition capacity

This file isolates the finite combinatorial bridge used by the body--pin
closure argument.  A fine surjective labelling gives a simple support whose
nonzero bundle multiplicities are assumed to be at most two.  The partition
condition then forces that support to contain a prescribed `(2,2)`-sparse
subgraph.

The key intermediate statement is a provenance-preserving aggregation
inequality: after any coarsening of the fine labels, capped capacity is at
most `2 M + s`, where `M` and `s` count the fine crossing occurrences and
their fine simple support.  Thus aggregation never creates an unaccounted
capacity contribution.
-/

namespace RB31E2E

private theorem pinCapacity_eq_two_mul_add_one_of_pos_le_two
    {m : ℕ} (hpos : 0 < m) (hle : m ≤ 2) :
    pinCapacity m = 2 * m + 1 := by
  interval_cases m <;> decide

private theorem pinCapacity_le_two_mul_add_support
    (M s : ℕ) (hLower : s ≤ M) (hUpper : M ≤ 2 * s) :
    pinCapacity M ≤ 2 * M + s := by
  rcases M with _ | _ | _ | M <;> simp [pinCapacity]
  all_goals omega

/-- Edges of the complete graph, regarded as unordered non-diagonal pairs. -/
def completeEdgeEquivSimpleEdge (I : Type*) [Fintype I] [DecidableEq I] :
    (⊤ : SimpleGraph I).edgeFinset ≃ SimpleEdge I where
  toFun b := ⟨b.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using b.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using e.2⟩
  left_inv b := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

@[simp]
theorem completeEdgeEquivSimpleEdge_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : (⊤ : SimpleGraph I).edgeFinset) :
    (completeEdgeEquivSimpleEdge I b).1 = b.1 := rfl

/-- Reindex a complete-graph edge sum by unordered non-diagonal pairs. -/
theorem sum_completeEdges_eq_sum_simpleEdges
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (f : Sym2 I → M) :
    (∑ b ∈ (⊤ : SimpleGraph I).edgeFinset, f b) =
      ∑ e : SimpleEdge I, f e.1 := by
  rw [← Finset.sum_attach]
  exact Fintype.sum_equiv (completeEdgeEquivSimpleEdge I)
    (fun b => f b.1) (fun e => f e.1) (fun _ => rfl)

namespace BodyPinIncidence

/-- Multiplicity carried by one fine simple label pair. -/
def fineMultiplicityOn (H : BodyPinIncidence) {I : Type*} [DecidableEq I]
    (label : H.Body → I) (e : SimpleEdge I) : ℕ :=
  H.bundleMultiplicityOn label e.1

/-- The simple support of all nonempty fine bundles. -/
noncomputable def fineSupportOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : SimpleEdgeSet I := by
  classical
  exact Finset.univ.filter fun e => 0 < H.fineMultiplicityOn label e

@[simp]
theorem mem_fineSupportOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) (e : SimpleEdge I) :
    e ∈ H.fineSupportOn label ↔ 0 < H.fineMultiplicityOn label e := by
  classical
  simp [fineSupportOn]

/-- Total multiplicity of the nonempty fine bundles. -/
noncomputable def fineMassOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : ℕ :=
  ∑ e ∈ H.fineSupportOn label, H.fineMultiplicityOn label e

/-- Capacity may be summed over the type of simple edges. -/
theorem capacityOn_eq_sum_simpleEdges (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) :
    H.capacityOn label =
      ∑ e : SimpleEdge I, pinCapacity (H.fineMultiplicityOn label e) := by
  unfold capacityOn fineMultiplicityOn
  exact sum_completeEdges_eq_sum_simpleEdges
    (fun b => pinCapacity (H.bundleMultiplicityOn label b))

/-- Zero fine bundles can be removed from a multiplicity sum. -/
theorem fineMassOn_eq_sum_simpleEdges (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) :
    H.fineMassOn label = ∑ e : SimpleEdge I, H.fineMultiplicityOn label e := by
  classical
  unfold fineMassOn fineSupportOn
  apply Finset.sum_subset (by simp)
  intro e heuniv henot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at henot
  exact Nat.eq_zero_of_not_pos henot

/-- On one- or two-pin support, the fine capacity is exactly `2 M + s`. -/
theorem capacityOn_eq_two_mul_fineMass_add_supportCard
    (H : BodyPinIncidence) {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.capacityOn label =
      2 * H.fineMassOn label + (H.fineSupportOn label).card := by
  classical
  rw [H.capacityOn_eq_sum_simpleEdges]
  calc
    (∑ e : SimpleEdge I, pinCapacity (H.fineMultiplicityOn label e)) =
        ∑ e ∈ H.fineSupportOn label,
          pinCapacity (H.fineMultiplicityOn label e) := by
      symm
      apply Finset.sum_subset (by simp)
      intro e heuniv henot
      have hm : ¬ 0 < H.fineMultiplicityOn label e := by
        simpa only [H.mem_fineSupportOn] using henot
      have hz : H.fineMultiplicityOn label e = 0 := Nat.eq_zero_of_not_pos hm
      simp [hz]
    _ = ∑ e ∈ H.fineSupportOn label,
          (2 * H.fineMultiplicityOn label e + 1) := by
      apply Finset.sum_congr rfl
      intro e he
      have hpos := (H.mem_fineSupportOn label e).mp he
      exact pinCapacity_eq_two_mul_add_one_of_pos_le_two hpos (hsmall e he)
    _ = 2 * H.fineMassOn label + (H.fineSupportOn label).card := by
      simp only [fineMassOn, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp

/-- Fine support edges which remain non-diagonal after a relabelling. -/
noncomputable def crossingFineSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) : SimpleEdgeSet I := by
  classical
  exact (H.fineSupportOn label).filter fun e => ¬(e.1.map ρ).IsDiag

@[simp]
theorem mem_crossingFineSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (e : SimpleEdge I) :
    e ∈ H.crossingFineSupportOn label ρ ↔
      e ∈ H.fineSupportOn label ∧ ¬(e.1.map ρ).IsDiag := by
  classical
  simp [crossingFineSupportOn]

/-- Total fine multiplicity which survives a relabelling as a crossing bundle. -/
noncomputable def crossingFineMassOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) : ℕ :=
  ∑ e ∈ H.crossingFineSupportOn label ρ,
    H.fineMultiplicityOn label e

/-- Fine support lying above one coarse unordered pair. -/
noncomputable def fibreSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) : SimpleEdgeSet I := by
  classical
  exact (H.fineSupportOn label).filter fun e => e.1.map ρ = b

@[simp]
theorem mem_fibreSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) (e : SimpleEdge I) :
    e ∈ H.fibreSupportOn label ρ b ↔
      e ∈ H.fineSupportOn label ∧ e.1.map ρ = b := by
  classical
  simp [fibreSupportOn]

/-- Fine multiplicity lying above one coarse unordered pair. -/
noncomputable def fibreMassOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) : ℕ :=
  ∑ e ∈ H.fibreSupportOn label ρ b, H.fineMultiplicityOn label e

private theorem sum_filter_simpleEdges_eq_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) :
    (∑ e : SimpleEdge I with e.1.map ρ = b,
        H.fineMultiplicityOn label e) = H.fibreMassOn label ρ b := by
  classical
  unfold fibreMassOn
  symm
  apply Finset.sum_subset
  · intro e he
    have he' := (H.mem_fibreSupportOn label ρ b e).mp he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact he'.2
  · intro e heBig heSmall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heBig
    have hnotSupport : e ∉ H.fineSupportOn label := by
      intro heSupport
      exact heSmall ((H.mem_fibreSupportOn label ρ b e).mpr ⟨heSupport, heBig⟩)
    have hnotPos : ¬ 0 < H.fineMultiplicityOn label e := by
      simpa only [H.mem_fineSupportOn] using hnotSupport
    exact Nat.eq_zero_of_not_pos hnotPos

/-- Coarse bundle multiplicity is the sum of the fine multiplicities above it. -/
theorem bundleMultiplicityOn_comp_eq_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K)
    (b : Sym2 K) (hb : b ∈ (⊤ : SimpleGraph K).edgeFinset) :
    H.bundleMultiplicityOn (ρ ∘ label) b = H.fibreMassOn label ρ b := by
  classical
  let T : Finset (Sym2 I) :=
    (⊤ : SimpleGraph I).edgeFinset.filter fun a => a.map ρ = b
  let pair : H.Pin → Sym2 I := fun p => s(label (H.left p), label (H.right p))
  have hraw := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset H.Pin) T pair
  have hbNotDiag : ¬ b.IsDiag := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using hb
  have hfilter :
      (Finset.univ.filter fun p : H.Pin => pair p ∈ T) =
        Finset.univ.filter fun p : H.Pin => (pair p).map ρ = b := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
    constructor
    · exact fun h => h.2
    · intro hp
      refine ⟨?_, hp⟩
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
        using fun hdiag => hbNotDiag (hp ▸ hdiag.map)
  have hraw' :
      (∑ a ∈ (⊤ : SimpleGraph I).edgeFinset with a.map ρ = b,
          H.bundleMultiplicityOn label a) =
        H.bundleMultiplicityOn (ρ ∘ label) b := by
    change (∑ a ∈ T,
        (Finset.univ.filter fun p : H.Pin => pair p = a).card) = _
    calc
      (∑ a ∈ T, (Finset.univ.filter fun p : H.Pin => pair p = a).card) =
          (Finset.univ.filter fun p : H.Pin => pair p ∈ T).card := hraw
      _ = (Finset.univ.filter fun p : H.Pin => (pair p).map ρ = b).card :=
        congrArg Finset.card hfilter
      _ = H.bundleMultiplicityOn (ρ ∘ label) b := by
        unfold bundleMultiplicityOn pair
        congr 1
  rw [← hraw']
  calc
    (∑ a ∈ (⊤ : SimpleGraph I).edgeFinset with a.map ρ = b,
        H.bundleMultiplicityOn label a) =
        ∑ e : SimpleEdge I with e.1.map ρ = b,
          H.fineMultiplicityOn label e := by
      rw [Finset.sum_filter, Finset.sum_filter]
      exact sum_completeEdges_eq_sum_simpleEdges
        (fun a => if a.map ρ = b then H.bundleMultiplicityOn label a else 0)
    _ = H.fibreMassOn label ρ b :=
      H.sum_filter_simpleEdges_eq_fibreMassOn label ρ b

theorem card_fibreSupportOn_le_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) :
    (H.fibreSupportOn label ρ b).card ≤ H.fibreMassOn label ρ b := by
  classical
  unfold fibreMassOn
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  exact (H.mem_fineSupportOn label e).mp
    ((H.mem_fibreSupportOn label ρ b e).mp he).1

theorem fibreMassOn_le_two_mul_card
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.fibreMassOn label ρ b ≤ 2 * (H.fibreSupportOn label ρ b).card := by
  classical
  unfold fibreMassOn
  calc
    (∑ e ∈ H.fibreSupportOn label ρ b, H.fineMultiplicityOn label e) ≤
        ∑ _e ∈ H.fibreSupportOn label ρ b, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact hsmall e ((H.mem_fibreSupportOn label ρ b e).mp he).1
    _ = 2 * (H.fibreSupportOn label ρ b).card := by simp [Nat.mul_comm]

theorem sum_fibreMassOn_eq_crossingFineMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) :
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset, H.fibreMassOn label ρ b) =
      H.crossingFineMassOn label ρ := by
  classical
  unfold fibreMassOn fibreSupportOn crossingFineMassOn crossingFineSupportOn
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using
    (Finset.sum_fiberwise_eq_sum_filter
      (H.fineSupportOn label) (⊤ : SimpleGraph K).edgeFinset
      (fun e : SimpleEdge I => e.1.map ρ)
      (fun e => H.fineMultiplicityOn label e))

theorem sum_card_fibreSupportOn_eq_card_crossingFineSupportOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) :
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
        (H.fibreSupportOn label ρ b).card) =
      (H.crossingFineSupportOn label ρ).card := by
  classical
  unfold fibreSupportOn crossingFineSupportOn
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (H.fineSupportOn label) (⊤ : SimpleGraph K).edgeFinset
      (fun e : SimpleEdge I => e.1.map ρ))

/--
The provenance-preserving aggregation inequality.  A coarse capped bundle
is paid for by the masses and support bits of the fine pairs which map to it.
-/
theorem capacityOn_comp_le_two_mul_crossingFineMass_add_card
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.capacityOn (ρ ∘ label) ≤
      2 * H.crossingFineMassOn label ρ +
        (H.crossingFineSupportOn label ρ).card := by
  classical
  unfold capacityOn
  calc
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
        pinCapacity (H.bundleMultiplicityOn (ρ ∘ label) b)) ≤
        ∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
          (2 * H.fibreMassOn label ρ b +
            (H.fibreSupportOn label ρ b).card) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [H.bundleMultiplicityOn_comp_eq_fibreMassOn label ρ b hb]
      exact pinCapacity_le_two_mul_add_support
        (H.fibreMassOn label ρ b) (H.fibreSupportOn label ρ b).card
        (H.card_fibreSupportOn_le_fibreMassOn label ρ b)
        (H.fibreMassOn_le_two_mul_card label ρ b hsmall)
    _ = 2 * H.crossingFineMassOn label ρ +
        (H.crossingFineSupportOn label ρ).card := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [H.sum_fibreMassOn_eq_crossingFineMassOn label ρ]
      rw [H.sum_card_fibreSupportOn_eq_card_crossingFineSupportOn label ρ]

theorem internalTo_iff_map_finpartitionBlock_isDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Finpartition (Finset.univ : Finset I)) (e : SimpleEdge I) :
    InternalTo P e ↔ (e.1.map (finpartitionBlock P)).IsDiag := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ a c =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨X, hX, hac⟩
        have ha : a ∈ X := hac (by simp [SimpleEdge.vertices])
        have hc : c ∈ X := hac (by simp [SimpleEdge.vertices])
        apply Subtype.ext
        exact ((P.part_eq_iff_mem hX).2 ha).trans
          ((P.part_eq_iff_mem hX).2 hc).symm
      · intro hblock
        let X : P.parts := ⟨P.part a, P.part_mem.mpr (by simp)⟩
        refine ⟨X.1, X.2, ?_⟩
        intro v hv
        simp only [SimpleEdge.vertices, Sym2.toFinset_mk_eq,
          Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact P.mem_part (by simp)
        · have hpart : P.part v = P.part a := by
            exact congr_arg Subtype.val hblock.symm
          change v ∈ P.part a
          rw [← hpart]
          exact P.mem_part (by simp)

theorem crossingFineSupportOn_finpartitionBlock
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    H.crossingFineSupportOn label (finpartitionBlock P) =
      crossEdges (H.fineSupportOn label) P := by
  classical
  ext e
  rw [H.mem_crossingFineSupportOn, mem_crossEdges]
  rw [internalTo_iff_map_finpartitionBlock_isDiag]

theorem crossingFineMassOn_finpartitionBlock
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    H.crossingFineMassOn label (finpartitionBlock P) =
      ∑ e ∈ crossEdges (H.fineSupportOn label) P,
        H.fineMultiplicityOn label e := by
  unfold crossingFineMassOn
  rw [H.crossingFineSupportOn_finpartitionBlock label P]

theorem sum_internalEdges_add_sum_crossEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : SimpleEdgeSet I)
    (P : Finpartition (Finset.univ : Finset I)) (w : SimpleEdge I → ℕ) :
    (∑ e ∈ internalEdges J P, w e) +
        (∑ e ∈ crossEdges J P, w e) = ∑ e ∈ J, w e := by
  classical
  unfold internalEdges crossEdges
  exact Finset.sum_filter_add_sum_filter_not J (InternalTo P) w

theorem card_internalEdges_le_sum_fineMultiplicity
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    (internalEdges (H.fineSupportOn label) P).card ≤
      ∑ e ∈ internalEdges (H.fineSupportOn label) P,
        H.fineMultiplicityOn label e := by
  classical
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  exact (H.mem_fineSupportOn label e).mp (mem_internalEdges.mp he).1

/-- The deficit which must be paid by a sparse null skeleton. -/
noncomputable def sparseSkeletonTarget (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  6 * (t - 1) - 2 * H.fineMassOn π

/--
The body--pin partition condition extracts a simple `(2,2)`-sparse null
skeleton whenever every nonempty fine bundle contains at most two pins.

The explicit hypothesis `2 ≤ t` is the weakest case needed by the
nontrivial equality-cellule argument.  The zero- and one-label cases have
target zero and are intentionally left out of this interface.
-/
theorem exists_sparse_nullSkeleton
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (ht : 2 ≤ t)
    (hpartition : H.PartitionCondition)
    (hsmall : ∀ e ∈ H.fineSupportOn π,
      H.fineMultiplicityOn π e ≤ 2) :
    ∃ F : SimpleEdgeSet (Fin t),
      F ⊆ H.fineSupportOn π ∧ Sparse22 F ∧
        F.card = H.sparseSkeletonTarget π := by
  classical
  let J : SimpleEdgeSet (Fin t) := H.fineSupportOn π
  let M : ℕ := H.fineMassOn π
  let R : ℕ := H.sparseSkeletonTarget π
  have hfine : 6 * (t - 1) ≤ 2 * M + J.card := by
    have h := hpartition t π hπ
    rw [← H.capacityOn_fin] at h
    rw [H.capacityOn_eq_two_mul_fineMass_add_supportCard π hsmall] at h
    exact h
  have hterms :
      ∀ P : Finpartition (Finset.univ : Finset (Fin t)),
        R ≤ sparsePartitionTerm J P := by
    intro P
    let q : ℕ := P.parts.card
    let C : SimpleEdgeSet (Fin t) := crossEdges J P
    let A : SimpleEdgeSet (Fin t) := internalEdges J P
    let MC : ℕ := ∑ e ∈ C, H.fineMultiplicityOn π e
    let MA : ℕ := ∑ e ∈ A, H.fineMultiplicityOn π e
    have hqle : q ≤ t := by
      simpa [q] using P.card_parts_le_card
    have hqpos : 0 < q := by
      let v : Fin t := ⟨0, by omega⟩
      have hv : P.part v ∈ P.parts := P.part_mem.mpr (by simp)
      exact Finset.card_pos.mpr ⟨P.part v, hv⟩
    have hcardSplit : A.card + C.card = J.card := by
      exact card_internalEdges_add_card_crossEdges J P
    have hmassSplit : MA + MC = M := by
      exact sum_internalEdges_add_sum_crossEdges J P
        (fun e => H.fineMultiplicityOn π e)
    have hAcardMass : A.card ≤ MA := by
      exact H.card_internalEdges_le_sum_fineMultiplicity π P
    have hcoarseSurj :
        Function.Surjective (finpartitionBlock P ∘ π) :=
      (finpartitionBlock_surjective P).comp hπ
    have hcoarseLower :
        6 * (q - 1) ≤ H.capacityOn (finpartitionBlock P ∘ π) := by
      let e : P.parts ≃ Fin q := P.parts.equivFin
      have hsurj : Function.Surjective (e ∘ finpartitionBlock P ∘ π) :=
        e.surjective.comp hcoarseSurj
      have h := hpartition q (e ∘ finpartitionBlock P ∘ π) hsurj
      rw [← H.capacityOn_fin] at h
      have heq := H.capacityOn_comp_equiv e (finpartitionBlock P ∘ π)
      simpa only [Function.comp_assoc, heq] using h
    have hcoarseUpper :
        H.capacityOn (finpartitionBlock P ∘ π) ≤ 2 * MC + C.card := by
      have h := H.capacityOn_comp_le_two_mul_crossingFineMass_add_card
        π (finpartitionBlock P) hsmall
      rw [H.crossingFineMassOn_finpartitionBlock π P,
        H.crossingFineSupportOn_finpartitionBlock π P] at h
      exact h
    have hcoarse : 6 * (q - 1) ≤ 2 * MC + C.card :=
      hcoarseLower.trans hcoarseUpper
    have htarget : R = 6 * (t - 1) - 2 * M := rfl
    rw [sparsePartitionTerm]
    simp only [Fintype.card_fin]
    change R ≤ 2 * (t - q) + C.card
    rw [htarget]
    by_cases hsmallInternal : A.card ≤ 2 * (t - q)
    · omega
    · have hlargeInternal : 2 * (t - q) ≤ MA := by omega
      omega
  have hextract := exists_sparse22_of_all_partition_terms J R hterms
  simpa [J, R] using hextract

end BodyPinIncidence

end RB31E2E
