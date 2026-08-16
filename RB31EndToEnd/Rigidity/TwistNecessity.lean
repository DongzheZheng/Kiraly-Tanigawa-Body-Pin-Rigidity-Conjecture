import RB31EndToEnd.Algebra.GroundedTwist
import RB31EndToEnd.Combinatorics.BodyPinCapacity

/-!
# Partition necessity for rigid body--twist systems

For a fixed surjective block labelling, we ground one block and group all
pin constraints by their unordered pair of block labels.  Each grouped
operator factors through one relative six-dimensional twist.  Its signed
pin evaluations have the same kernel as ordinary pin evaluations, so the
proved `0,3,5,6` bundle bounds apply without any rank hypothesis.
-/

namespace RB31E2E

/-- The rank of a finite product of linear maps is at most the sum of the
ranks of its coordinate maps. -/
theorem finrank_range_pi_le_sum
    {k I V : Type*} [Field k] [Fintype I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : I → Type*} [(i : I) → AddCommGroup (W i)]
    [(i : I) → Module k (W i)]
    (f : (i : I) → V →ₗ[k] W i) :
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
      ∑ i, Module.finrank k (LinearMap.range (f i)) := by
  classical
  let Φ : LinearMap.range (LinearMap.pi f) →ₗ[k]
      ((i : I) → LinearMap.range (f i)) :=
    { toFun := fun y i ↦ ⟨y.1 i, by
        obtain ⟨x, hx⟩ := y.2
        refine ⟨x, ?_⟩
        simpa using congrFun hx i⟩
      map_add' := by
        intro y z
        funext i
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a y
        funext i
        apply Subtype.ext
        rfl }
  have hΦ : Function.Injective Φ := by
    intro y z hyz
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hyz i)
  calc
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
        Module.finrank k ((i : I) → LinearMap.range (f i)) :=
      LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ i, Module.finrank k (LinearMap.range (f i)) := by
      rw [Module.finrank_pi_fintype]

namespace Twist

variable {k I : Type*} [Field k]

/-- The proved bundle bound, transported from `Fin m` to an arbitrary finite
occurrence type without losing occurrence provenance. -/
theorem finrank_range_bundleLinear_le_pinCapacity_card
    [Fintype I] (p : I → Vec3 k) :
    Module.finrank k (LinearMap.range (bundleLinear p)) ≤
      pinCapacity (Fintype.card I) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q : Fin (Fintype.card I) → Vec3 k := p ∘ e.symm
  have hker : LinearMap.ker (bundleLinear p) =
      LinearMap.ker (bundleLinear q) := by
    ext X
    constructor
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext j
      have hj := congrFun hX (e.symm j)
      simpa [q] using hj
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext i
      have hi := congrFun hX (e i)
      simpa [q] using hi
  have hp := (bundleLinear p).finrank_range_add_finrank_ker
  have hq := (bundleLinear q).finrank_range_add_finrank_ker
  rw [hker] at hp
  have hrange : Module.finrank k (LinearMap.range (bundleLinear p)) =
      Module.finrank k (LinearMap.range (bundleLinear q)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity (Fintype.card I) q

/-- Coordinatewise signed evaluation of one relative twist. -/
noncomputable def signedBundleLinear [Fintype I]
    (p : I → Vec3 k) (sign : I → k) :
    Twist k →ₗ[k] (I → Vec3 k) :=
  LinearMap.pi fun i ↦ sign i • evalLinear (p i)

@[simp] theorem signedBundleLinear_apply [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (X : Twist k) (i : I) :
    signedBundleLinear p sign X i = sign i • eval X (p i) := by
  simp [signedBundleLinear]

/-- Nonzero coordinate signs do not change the kernel of bundle evaluation. -/
theorem ker_signedBundleLinear_eq [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    LinearMap.ker (signedBundleLinear p sign) =
      LinearMap.ker (bundleLinear p) := by
  ext X
  constructor
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [signedBundleLinear_apply, Pi.zero_apply] at hi
    exact (smul_eq_zero.mp hi).resolve_left (hsign i)
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [bundleLinear_apply, Pi.zero_apply] at hi
    simp [signedBundleLinear_apply, hi]

/-- The `0,3,5,6` bound is invariant under independent nonzero signs on the
occurrence coordinates. -/
theorem finrank_range_signedBundleLinear_le_pinCapacity_card [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    Module.finrank k (LinearMap.range (signedBundleLinear p sign)) ≤
      pinCapacity (Fintype.card I) := by
  have hker := ker_signedBundleLinear_eq p sign hsign
  have hs := (signedBundleLinear p sign).finrank_range_add_finrank_ker
  have hu := (bundleLinear p).finrank_range_add_finrank_ker
  rw [hker] at hs
  have hrange : Module.finrank k (LinearMap.range (signedBundleLinear p sign)) =
      Module.finrank k (LinearMap.range (bundleLinear p)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity_card p

end Twist

namespace BodyPinIncidence

/-- An unordered pair of distinct labels in a `t`-block partition. -/
abbrev PartitionEdge (t : ℕ) :=
  ↑((⊤ : SimpleGraph (Fin t)).edgeFinset)

/-- The occurrence type of pins belonging to one unordered block bundle. -/
abbrev PartitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :=
  ↑(Finset.univ.filter fun e : H.Pin ↦
    s(π (H.left e), π (H.right e)) = b.1)

@[simp] theorem card_partitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    Fintype.card (H.PartitionBundlePin π b) =
      H.unorderedBundleMultiplicity π b.1 := by
  rw [Fintype.card_subtype]
  simp [PartitionBundlePin, unorderedBundleMultiplicity]

theorem partitionEdge_out_mk {t : ℕ} (b : PartitionEdge t) :
    s(b.1.out.1, b.1.out.2) = b.1 :=
  Quot.out_eq b.1

theorem partitionEdge_out_ne {t : ℕ} (b : PartitionEdge t) :
    b.1.out.1 ≠ b.1.out.2 := by
  intro h
  have hdiag : b.1.IsDiag := by
    rw [← partitionEdge_out_mk b, Sym2.mk_isDiag_iff]
    exact h
  exact (SimpleGraph.not_isDiag_of_mem_edgeFinset b.2) hdiag

/-- The point coordinates in one occurrence-level bundle. -/
def partitionBundlePoint (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → Vec3 ℝ :=
  fun e ↦ p e.1

/-- Sign comparing the stored orientation of a pin occurrence with the
orientation selected by `Sym2.out` for its unordered block bundle. -/
noncomputable def partitionBundleSign (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → ℝ :=
  fun e ↦ if π (H.left e.1) = b.1.out.1 then 1 else -1

theorem partitionBundleSign_ne_zero (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.partitionBundleSign π b e ≠ 0 := by
  classical
  by_cases h : π (H.left e.1) = b.1.out.1 <;>
    simp [partitionBundleSign, h]

/-- All pin constraints in one unordered block bundle, before grounding. -/
noncomputable def blockBundleOperator (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    (Fin t → Twist ℝ) →ₗ[ℝ] (H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e.1)).comp
      (assignmentDifferenceLinear (π (H.left e.1)) (π (H.right e.1)))

@[simp] theorem blockBundleOperator_apply (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    H.blockBundleOperator π p b X e =
      Twist.eval
        (X (π (H.left e.1)) - X (π (H.right e.1))) (p e.1) := by
  simp [blockBundleOperator, assignmentDifferenceLinear]

/-- The oriented relative twist of every occurrence is the selected bundle
relative twist, multiplied by its explicit sign. -/
theorem occurrenceDifference_eq_sign_smul (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    X (π (H.left e.1)) - X (π (H.right e.1)) =
      H.partitionBundleSign π b e • (X b.1.out.1 - X b.1.out.2) := by
  classical
  have he : s(π (H.left e.1), π (H.right e.1)) = b.1 :=
    (Finset.mem_filter.mp e.2).2
  have he' : s(π (H.left e.1), π (H.right e.1)) =
      s(b.1.out.1, b.1.out.2) :=
    he.trans (partitionEdge_out_mk b).symm
  rcases Sym2.eq_iff.mp he' with h | h
  · rcases h with ⟨hl, hr⟩
    simp [partitionBundleSign, hl, hr]
  · rcases h with ⟨hl, hr⟩
    have hne : b.1.out.2 ≠ b.1.out.1 := (partitionEdge_out_ne b).symm
    simp [partitionBundleSign, hl, hr, hne]

/-- Explicit factorization of a bundle through one relative twist and its
signed occurrence evaluations. -/
theorem blockBundleOperator_eq_signed_comp (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.blockBundleOperator π p b =
      (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
        (H.partitionBundleSign π b)).comp
        (assignmentDifferenceLinear b.1.out.1 b.1.out.2) := by
  apply LinearMap.ext
  intro X
  funext e
  rw [H.blockBundleOperator_apply]
  simp only [LinearMap.comp_apply, Twist.signedBundleLinear_apply,
    assignmentDifferenceLinear]
  rw [H.occurrenceDifference_eq_sign_smul π b X e]
  exact (Twist.evalLinear (p e.1)).map_smul
    (H.partitionBundleSign π b e) (X b.1.out.1 - X b.1.out.2)

/-- Each unordered bundle pays at most its already-proved `0,3,5,6`
capacity, with no genericity or rank premise. -/
theorem finrank_range_blockBundleOperator_le_capacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    Module.finrank ℝ (LinearMap.range (H.blockBundleOperator π p b)) ≤
      pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
  rw [H.blockBundleOperator_eq_signed_comp]
  calc
    Module.finrank ℝ
        (LinearMap.range
          ((Twist.signedBundleLinear (H.partitionBundlePoint π p b)
            (H.partitionBundleSign π b)).comp
            (assignmentDifferenceLinear b.1.out.1 b.1.out.2))) ≤
        Module.finrank ℝ
          (LinearMap.range
            (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
              (H.partitionBundleSign π b))) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ pinCapacity (Fintype.card (H.PartitionBundlePin π b)) :=
      Twist.finrank_range_signedBundleLinear_le_pinCapacity_card _ _
        (H.partitionBundleSign_ne_zero π b)
    _ = pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      rw [H.card_partitionBundlePin]

/-- Rigidity pulls back from bodies to any surjective quotient of the body
set: a block-constant motion is in particular a body motion. -/
theorem twistRigidAt_blocks_of_surjective (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (hπ : Function.Surjective π)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    TwistRigidAt (π ∘ H.left) (π ∘ H.right) p := by
  intro X hX
  have hBody : IsTwistMotion H.left H.right p (X ∘ π) := by
    intro e
    exact hX e
  obtain ⟨Y, hY⟩ := hRigid (X ∘ π) hBody
  refine ⟨Y, ?_⟩
  funext i
  obtain ⟨body, hbody⟩ := hπ i
  have hi := congrFun hY body
  simpa [Function.comp_apply, hbody] using hi

/-- All crossing constraints of a grounded block assignment, grouped by
their unordered block bundle.  Internal pins are omitted because a
block-constant twist makes their relative twist identically zero. -/
noncomputable def groupedGroundedBlockOperator (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    (OffRoot root → Twist ℝ) →ₗ[ℝ]
      ((b : PartitionEdge t) → H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun b ↦
    (H.blockBundleOperator π p b).comp (extendGroundedLinear root)

@[simp] theorem groupedGroundedBlockOperator_apply
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t)
    (X : OffRoot root → Twist ℝ) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.groupedGroundedBlockOperator π p root X b e =
      Twist.eval
        (extendGrounded root X (π (H.left e.1)) -
          extendGrounded root X (π (H.right e.1))) (p e.1) := by
  simp [groupedGroundedBlockOperator, H.blockBundleOperator_apply,
    extendGroundedLinear]

/-- Under pointwise twist rigidity, the grouped grounded block operator is
injective.  This is the lower-rank half of partition necessity. -/
theorem groupedGroundedBlockOperator_injective_of_twistRigidAt
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    Function.Injective (H.groupedGroundedBlockOperator π p root) := by
  classical
  have hBlockRigid : TwistRigidAt (π ∘ H.left) (π ∘ H.right) p :=
    H.twistRigidAt_blocks_of_surjective π hπ p hRigid
  have hGroundInjective : Function.Injective
      (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p) :=
    (groundedPinOperator_injective_iff_twistRigidAt
      root (π ∘ H.left) (π ∘ H.right) p).2 hBlockRigid
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.2
  intro X hX
  have hGroundZero :
      groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p X = 0 := by
    funext e
    by_cases heq : π (H.left e) = π (H.right e)
    · simp [groundedPinOperator_apply, Function.comp_apply, heq,
        Twist.eval, Vec3.cross]
    · let b : PartitionEdge t :=
        ⟨s(π (H.left e), π (H.right e)), by
          simp [Sym2.mk_isDiag_iff, heq]⟩
      let eb : H.PartitionBundlePin π b := ⟨e, by
        simp [PartitionBundlePin, b]⟩
      have hGrouped := congrFun (congrFun hX b) eb
      simpa [groundedPinOperator_apply, Function.comp_apply,
        H.groupedGroundedBlockOperator_apply] using hGrouped
  exact hGroundInjective (by simpa using hGroundZero)

/-- The grouped grounded operator has at least the full dimension of the
grounded block-twist space. -/
theorem six_mul_pred_le_groupedGroundedBlockOperator_rank
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    6 * (t - 1) ≤
      Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) := by
  have hinj := H.groupedGroundedBlockOperator_injective_of_twistRigidAt
    π hπ p hRigid root
  have hker : LinearMap.ker (H.groupedGroundedBlockOperator π p root) = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hRN := (H.groupedGroundedBlockOperator π p root).finrank_range_add_finrank_ker
  rw [hker] at hRN
  simp only [finrank_bot, add_zero] at hRN
  have hcard : Fintype.card (OffRoot root) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin t ↦ i = root)]
    simp
  have hdomain : Module.finrank ℝ (OffRoot root → Twist ℝ) =
      6 * (t - 1) := by
    rw [Module.finrank_pi_fintype]
    simp [hcard, Nat.mul_comm]
  rw [← hdomain, ← hRN]

/-- The grouped operator's rank is at most the sum of the proved capacities
of its unordered bundles. -/
theorem groupedGroundedBlockOperator_rank_le_partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
      H.partitionCapacity π := by
  classical
  calc
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
        ∑ b : PartitionEdge t,
          Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) := by
      exact finrank_range_pi_le_sum fun b ↦
        (H.blockBundleOperator π p b).comp (extendGroundedLinear root)
    _ ≤ ∑ b : PartitionEdge t,
        pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) ≤
            Module.finrank ℝ
              (LinearMap.range (H.blockBundleOperator π p b)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
        _ ≤ pinCapacity (H.unorderedBundleMultiplicity π b.1) :=
          H.finrank_range_blockBundleOperator_le_capacity π p b
    _ = H.partitionCapacity π := by
      unfold partitionCapacity
      symm
      apply Finset.sum_subtype
      intro b
      rfl

/-- Pointwise twist rigidity forces every body partition to satisfy the
body--pin `0,3,5,6` capacity inequality. -/
theorem partitionCondition_of_twistRigidAt (H : BodyPinIncidence)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    H.PartitionCondition := by
  intro t π hπ
  by_cases ht : t = 0
  · subst t
    simp
  · let root : Fin t := ⟨0, Nat.pos_of_ne_zero ht⟩
    exact (H.six_mul_pred_le_groupedGroundedBlockOperator_rank
      π hπ p hRigid root).trans
        (H.groupedGroundedBlockOperator_rank_le_partitionCapacity π p root)

/-- Existential rigid twist realizability implies the complete partition
condition. -/
theorem partitionCondition_of_hasRigidTwistRealization
    (H : BodyPinIncidence)
    (hRigid : HasRigidTwistRealization (k := ℝ) H.left H.right) :
    H.PartitionCondition := by
  obtain ⟨p, hp⟩ := hRigid
  exact H.partitionCondition_of_twistRigidAt p hp

end BodyPinIncidence

end RB31E2E
