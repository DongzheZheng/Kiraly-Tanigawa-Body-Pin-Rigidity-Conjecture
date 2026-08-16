import RB31EndToEnd.Combinatorics.BodyPinCapacity
import Mathlib.Order.Partition.Finpartition

/-!
# Body--pin capacities indexed by ordinary finite partitions

The specification uses surjective labels `Body → Fin t`.  This file
proves that the same condition can be stated intrinsically using
`Finpartition univ`.  The constructions also cover the empty body type:
then both the label type and the finpartition have zero blocks.
-/

namespace RB31E2E

namespace BodyPinIncidence

/-- Bundle multiplicity for an arbitrary finite label type. -/
def bundleMultiplicityOn (H : BodyPinIncidence) {I : Type*} [DecidableEq I]
    (label : H.Body → I) (b : Sym2 I) : ℕ :=
  (Finset.univ.filter fun e => s(label (H.left e), label (H.right e)) = b).card

/-- Unordered capacity for an arbitrary finite label type. -/
def capacityOn (H : BodyPinIncidence) {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : ℕ :=
  ∑ b ∈ (⊤ : SimpleGraph I).edgeFinset,
    pinCapacity (H.bundleMultiplicityOn label b)

theorem bundleMultiplicityOn_fin {t : ℕ} (H : BodyPinIncidence)
    (label : H.Body → Fin t) (b : Sym2 (Fin t)) :
    H.bundleMultiplicityOn label b = H.unorderedBundleMultiplicity label b := rfl

theorem capacityOn_fin {t : ℕ} (H : BodyPinIncidence) (label : H.Body → Fin t) :
    H.capacityOn label = H.partitionCapacity label := rfl

/-- An equivalence induces an equivalence on unordered pairs. -/
def sym2Equiv {I K : Type*} (e : I ≃ K) : Sym2 I ≃ Sym2 K where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := Sym2.ind (by simp)
  right_inv := Sym2.ind (by simp)

@[simp]
theorem sym2Equiv_apply {I K : Type*} (e : I ≃ K) (b : Sym2 I) :
    sym2Equiv e b = b.map e := rfl

theorem bundleMultiplicityOn_comp_equiv
    (H : BodyPinIncidence) {I K : Type*} [DecidableEq I] [DecidableEq K]
    (e : I ≃ K) (label : H.Body → I) (b : Sym2 I) :
    H.bundleMultiplicityOn (e ∘ label) (sym2Equiv e b) =
      H.bundleMultiplicityOn label b := by
  unfold bundleMultiplicityOn
  congr 1
  ext pin
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    sym2Equiv_apply]
  change Sym2.map e s(label (H.left pin), label (H.right pin)) = Sym2.map e b ↔ _
  exact (Sym2.map.injective e.injective).eq_iff

theorem capacityOn_comp_equiv
    (H : BodyPinIncidence) {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : I ≃ K) (label : H.Body → I) :
    H.capacityOn (e ∘ label) = H.capacityOn label := by
  unfold capacityOn
  symm
  apply Finset.sum_equiv (sym2Equiv e)
  · intro b
    simp only [sym2Equiv_apply, SimpleGraph.mem_edgeFinset]
    rw [SimpleGraph.edgeSet_top, SimpleGraph.edgeSet_top]
    exact not_congr (Sym2.isDiag_map e.injective).symm
  · intro b hb
    rw [bundleMultiplicityOn_comp_equiv]

/-- The block of an element as a member of the finite type of parts. -/
def finpartitionBlock {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) (a : A) : P.parts :=
  ⟨P.part a, P.part_mem.mpr (by simp)⟩

theorem finpartitionBlock_surjective {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) :
    Function.Surjective (finpartitionBlock P) := by
  intro X
  obtain ⟨a, ha, hpart⟩ := P.part_surjOn X.property
  exact ⟨a, Subtype.ext hpart⟩

/-- Multiplicity of an unordered pair of ordinary finpartition blocks. -/
def finpartitionBundleMultiplicity (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) (b : Sym2 P.parts) : ℕ :=
  H.bundleMultiplicityOn (finpartitionBlock P) b

/-- Total capped capacity over unordered distinct blocks of `P`. -/
def finpartitionCapacity (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) : ℕ :=
  H.capacityOn (finpartitionBlock P)

theorem finpartitionBlock_eq_iff_mem {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) (a : A) (X : P.parts) :
    finpartitionBlock P a = X ↔ a ∈ X.1 := by
  rw [Subtype.ext_iff]
  exact P.part_eq_iff_mem X.property

/-- Intrinsic bundle multiplicity is the original crossing multiplicity of its two blocks. -/
theorem finpartitionBundleMultiplicity_mk (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) (A B : P.parts) :
    H.finpartitionBundleMultiplicity P s(A, B) = H.crossingMultiplicity A.1 B.1 := by
  unfold finpartitionBundleMultiplicity bundleMultiplicityOn crossingMultiplicity
  congr 1
  ext pin
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff]
  simp only [finpartitionBlock_eq_iff_mem]

theorem finpartitionCapacity_eq_sum (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) :
    H.finpartitionCapacity P =
      ∑ b ∈ (⊤ : SimpleGraph P.parts).edgeFinset,
        pinCapacity (H.finpartitionBundleMultiplicity P b) := rfl

/-- Canonical consecutive labels for the blocks of an ordinary finpartition. -/
noncomputable def finpartitionLabel (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) : H.Body → Fin P.parts.card :=
  P.parts.equivFin ∘ finpartitionBlock P

theorem finpartitionLabel_surjective (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) :
    Function.Surjective (H.finpartitionLabel P) :=
  P.parts.equivFin.surjective.comp (finpartitionBlock_surjective P)

/-- Intrinsic block capacity equals capacity after canonical finite relabelling. -/
theorem finpartitionCapacity_eq_partitionCapacity_label
    (H : BodyPinIncidence) (P : Finpartition (Finset.univ : Finset H.Body)) :
    H.finpartitionCapacity P = H.partitionCapacity (H.finpartitionLabel P) := by
  rw [← H.capacityOn_fin]
  exact (H.capacityOn_comp_equiv P.parts.equivFin (finpartitionBlock P)).symm

/-- The fibre of a finite block label. -/
def labelFiber (H : BodyPinIncidence) {t : ℕ} (label : H.Body → Fin t)
    (i : Fin t) : Finset H.Body :=
  Finset.univ.filter fun a => label a = i

@[simp]
theorem mem_labelFiber (H : BodyPinIncidence) {t : ℕ} (label : H.Body → Fin t)
    (i : Fin t) (a : H.Body) : a ∈ H.labelFiber label i ↔ label a = i := by
  simp [labelFiber]

theorem labelFiber_nonempty (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    (H.labelFiber label i).Nonempty := by
  obtain ⟨a, ha⟩ := hlabel i
  exact ⟨a, (H.mem_labelFiber label i a).mpr ha⟩

theorem labelFiber_injective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Injective (H.labelFiber label) := by
  intro i j hij
  obtain ⟨a, hai⟩ := H.labelFiber_nonempty label hlabel i
  have haj : a ∈ H.labelFiber label j := by rwa [← hij]
  exact (H.mem_labelFiber label i a).mp hai |>.symm.trans
    ((H.mem_labelFiber label j a).mp haj)

def labelFiberEmbedding (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Fin t ↪ Finset H.Body :=
  ⟨H.labelFiber label, H.labelFiber_injective label hlabel⟩

/-- The ordinary finpartition whose blocks are the nonempty label fibres. -/
def finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Finpartition (Finset.univ : Finset H.Body) :=
  Finpartition.ofExistsUnique
    (Finset.univ.map (H.labelFiberEmbedding label hlabel))
    (by
      intro X hX
      exact Finset.subset_univ X)
    (by
      intro a ha
      refine ⟨H.labelFiber label (label a), ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_map.mpr ⟨label a, Finset.mem_univ _, rfl⟩
      · exact (H.mem_labelFiber label (label a) a).mpr rfl
      · intro X hX
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hX.1
        have haX := hX.2
        have hai := (H.mem_labelFiber label i a).mp haX
        subst i
        rfl)
    (by
      intro hempty
      obtain ⟨i, hi, hifiber⟩ := Finset.mem_map.mp hempty
      have hne := H.labelFiber_nonempty label hlabel i
      have hifiber' : H.labelFiber label i = ∅ := by
        simpa [labelFiberEmbedding] using hifiber
      rw [hifiber'] at hne
      exact Finset.not_nonempty_empty hne)

@[simp]
theorem finpartitionOfSurjection_parts (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    (H.finpartitionOfSurjection label hlabel).parts =
      Finset.univ.map (H.labelFiberEmbedding label hlabel) := rfl

@[simp]
theorem card_parts_finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    (H.finpartitionOfSurjection label hlabel).parts.card = t := by
  rw [H.finpartitionOfSurjection_parts]
  simp

/-- The fibre with label `i`, regarded as a block of the fibre partition. -/
def labelBlock (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    (H.finpartitionOfSurjection label hlabel).parts :=
  ⟨H.labelFiber label i, by
    rw [H.finpartitionOfSurjection_parts]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem labelBlock_injective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Injective (H.labelBlock label hlabel) := by
  intro i j hij
  apply H.labelFiber_injective label hlabel
  exact congr_arg Subtype.val hij

theorem labelBlock_surjective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Surjective (H.labelBlock label hlabel) := by
  intro X
  have hX : X.1 ∈ Finset.univ.map (H.labelFiberEmbedding label hlabel) := by
    simpa only [H.finpartitionOfSurjection_parts] using X.property
  obtain ⟨i, hi, hiX⟩ := Finset.mem_map.mp hX
  refine ⟨i, Subtype.ext ?_⟩
  simpa [labelBlock, labelFiberEmbedding] using hiX

/-- Labels are equivalent to the blocks of their fibre partition. -/
noncomputable def labelEquivBlocks (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Fin t ≃ (H.finpartitionOfSurjection label hlabel).parts :=
  Equiv.ofBijective (H.labelBlock label hlabel)
    ⟨H.labelBlock_injective label hlabel, H.labelBlock_surjective label hlabel⟩

@[simp]
theorem labelEquivBlocks_apply (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    H.labelEquivBlocks label hlabel i = H.labelBlock label hlabel i := rfl

theorem finpartitionBlock_eq_labelEquivBlocks (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (a : H.Body) :
    finpartitionBlock (H.finpartitionOfSurjection label hlabel) a =
      H.labelEquivBlocks label hlabel (label a) := by
  rw [H.labelEquivBlocks_apply]
  apply Subtype.ext
  exact (H.finpartitionOfSurjection label hlabel).part_eq_of_mem
    (H.labelBlock label hlabel (label a)).property
    ((H.mem_labelFiber label (label a) a).mpr rfl)

/-- The fibre finpartition and its original surjective labelling have equal capacity. -/
theorem finpartitionCapacity_finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    H.finpartitionCapacity (H.finpartitionOfSurjection label hlabel) =
      H.partitionCapacity label := by
  let P := H.finpartitionOfSurjection label hlabel
  let e := H.labelEquivBlocks label hlabel
  have hblock : finpartitionBlock P = e ∘ label := by
    funext a
    exact H.finpartitionBlock_eq_labelEquivBlocks label hlabel a
  unfold finpartitionCapacity
  rw [hblock, H.capacityOn_comp_equiv, H.capacityOn_fin]

/-- The intrinsic partition condition over all ordinary finpartitions. -/
def FinpartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ P : Finpartition (Finset.univ : Finset H.Body),
    6 * (P.parts.card - 1) ≤ H.finpartitionCapacity P

/--
Surjective finite labels and ordinary finpartitions give exactly the same
body--pin partition condition.  No nonemptiness hypothesis is needed.
-/
theorem partitionCondition_iff_finpartitionCondition (H : BodyPinIncidence) :
    H.PartitionCondition ↔ H.FinpartitionCondition := by
  constructor
  · intro hlabelled P
    have h := hlabelled P.parts.card (H.finpartitionLabel P)
      (H.finpartitionLabel_surjective P)
    rw [← H.finpartitionCapacity_eq_partitionCapacity_label] at h
    exact h
  · intro hparts t label hlabel
    have h := hparts (H.finpartitionOfSurjection label hlabel)
    rw [H.card_parts_finpartitionOfSurjection,
      H.finpartitionCapacity_finpartitionOfSurjection] at h
    exact h

end BodyPinIncidence

end RB31E2E
