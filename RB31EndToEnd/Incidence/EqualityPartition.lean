import RB31EndToEnd.Combinatorics.BodyPinFinpartition
import RB31EndToEnd.NullCellule.GroundScale

/-!
# Exact equality partitions with provenance

Every finite twist assignment canonically determines a `Finpartition` by
equality of its values.  The finite type of parts then carries an injective
block-value map.  This is the formal label layer used by the fixed-stratum
incidence argument; no arbitrary quotient representatives remain visible in
the resulting theorems.
-/

namespace RB31E2E

noncomputable section

variable {k W : Type*} [Field k] [Fintype W] [DecidableEq W]

/-- Equality of values as a setoid on provenance labels. -/
def equalitySetoid (X : W → Twist k) : Setoid W :=
  Setoid.ker X

/-- The canonical finite partition into exact equality cellules. -/
def equalityPartition (X : W → Twist k) :
    Finpartition (Finset.univ : Finset W) := by
  classical
  exact Finpartition.ofSetoid (equalitySetoid X)

omit [Field k] in
@[simp] theorem mem_equalityPartition_part_iff (X : W → Twist k) (u v : W) :
    u ∈ (equalityPartition X).part v ↔ X u = X v := by
  classical
  simp [equalityPartition, equalitySetoid,
    Finpartition.mem_part_ofSetoid_iff_rel, eq_comm]

omit [Field k] in
theorem equalityPartition_part_eq_iff (X : W → Twist k) (u v : W) :
    (equalityPartition X).part u = (equalityPartition X).part v ↔
      X u = X v := by
  constructor
  · intro hpart
    have hu : u ∈ (equalityPartition X).part v := by
      rw [← hpart]
      exact (equalityPartition X).mem_part (by simp)
    exact (mem_equalityPartition_part_iff X u v).mp hu
  · intro hX
    ext w
    rw [mem_equalityPartition_part_iff, mem_equalityPartition_part_iff,
      hX]

/-- A canonical representative of one equality block. -/
def equalityBlockRepresentative (X : W → Twist k)
    (B : (equalityPartition X).parts) : W :=
  Classical.choose
    ((equalityPartition X).nonempty_of_mem_parts B.property)

omit [Field k] in
theorem equalityBlockRepresentative_mem (X : W → Twist k)
    (B : (equalityPartition X).parts) :
    equalityBlockRepresentative X B ∈ B.1 :=
  Classical.choose_spec
    ((equalityPartition X).nonempty_of_mem_parts B.property)

/-- The twist value carried by a block; the representative is hidden behind
the proof that the value is independent of it. -/
def equalityBlockValue (X : W → Twist k)
    (B : (equalityPartition X).parts) : Twist k :=
  X (equalityBlockRepresentative X B)

omit [Field k] in
@[simp] theorem equalityBlockValue_finpartitionBlock
    (X : W → Twist k) (w : W) :
    equalityBlockValue X
        (BodyPinIncidence.finpartitionBlock (equalityPartition X) w) = X w := by
  unfold equalityBlockValue
  have hmem := equalityBlockRepresentative_mem X
    (BodyPinIncidence.finpartitionBlock (equalityPartition X) w)
  have hsame : X (equalityBlockRepresentative X
      (BodyPinIncidence.finpartitionBlock (equalityPartition X) w)) = X w := by
    apply (mem_equalityPartition_part_iff X _ w).mp
    simpa [BodyPinIncidence.finpartitionBlock] using hmem
  exact hsame

omit [Field k] in
/-- Distinct equality blocks have distinct twist values. -/
theorem equalityBlockValue_injective (X : W → Twist k) :
    Function.Injective (equalityBlockValue X) := by
  intro A B hAB
  obtain ⟨a, ha⟩ :=
    BodyPinIncidence.finpartitionBlock_surjective (equalityPartition X) A
  obtain ⟨b, hb⟩ :=
    BodyPinIncidence.finpartitionBlock_surjective (equalityPartition X) B
  subst A
  subst B
  apply Subtype.ext
  apply (equalityPartition_part_eq_iff X a b).mpr
  simpa using hAB

/-- Ground the block values at a selected root block. -/
def groundedEqualityBlockValue (X : W → Twist k)
    (root : (equalityPartition X).parts) :
    (equalityPartition X).parts → Twist k :=
  fun B ↦ equalityBlockValue X B - equalityBlockValue X root

@[simp] theorem groundedEqualityBlockValue_root (X : W → Twist k)
    (root : (equalityPartition X).parts) :
    groundedEqualityBlockValue X root root = 0 := by
  simp [groundedEqualityBlockValue]

theorem groundedEqualityBlockValue_injective (X : W → Twist k)
    (root : (equalityPartition X).parts) :
    Function.Injective (groundedEqualityBlockValue X root) := by
  intro A B hAB
  apply equalityBlockValue_injective X
  exact sub_left_injective hAB

/-- If the equality partition has another block, its grounded block-value
assignment is nonzero, so the common `G_m` scaling action is free. -/
theorem groundedEqualityBlockValue_unitsScale_injective
    (X : W → Twist k) (root other : (equalityPartition X).parts)
    (hne : other ≠ root) :
    Function.Injective (fun a : kˣ ↦
      ((a : k) • groundedEqualityBlockValue X root :
        (equalityPartition X).parts → Twist k)) := by
  apply units_commonScale_injective_of_ne_zero
  apply ne_zero_of_grounded_of_ne
    (groundedEqualityBlockValue_root X root)
  exact fun h ↦ hne
    ((groundedEqualityBlockValue_injective X root) h)

end

end RB31E2E
