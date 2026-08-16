import RB31EndToEnd.Combinatorics.Sparse22.Basic
import RB31EndToEnd.Linear.Vec3Twist

/-!
# Distinct Split--Klein null-difference configurations

This is the point-set semantics of the null cellule used in the
algebraic-geometric layer.  It is intentionally independent of any
dimension claim.
-/

namespace RB31E2E

variable {k V : Type*} [CommRing k] [DecidableEq V]

/-- The Split--Klein null-difference equation attached to an unordered edge. -/
def IsNullOnEdge (X : V → Twist k) (e : SimpleEdge V) : Prop :=
  Sym2.lift ⟨fun u v ↦ Twist.splitKlein (X u - X v) = 0, by
    intro u v
    apply propext
    change Twist.splitKlein (X u - X v) = 0 ↔
      Twist.splitKlein (X v - X u) = 0
    rw [Twist.splitKlein_sub_comm]⟩ e.1

/-- All equations attached to the selected simple edge set hold. -/
def IsNullDifferenceConfiguration (F : SimpleEdgeSet V) (X : V → Twist k) : Prop :=
  ∀ e ∈ F, IsNullOnEdge X e

/-- The open condition that all labelled twists are pairwise distinct. -/
def IsDistinctConfiguration (X : V → Twist k) : Prop :=
  Function.Injective X

/-- Membership in the distinct null-difference cellule. -/
def InNullCellule (F : SimpleEdgeSet V) (X : V → Twist k) : Prop :=
  IsDistinctConfiguration X ∧ IsNullDifferenceConfiguration F X

omit [DecidableEq V] in
@[simp] theorem isNullOnEdge_mk (X : V → Twist k) (u v : V) (huv : u ≠ v) :
    IsNullOnEdge X ⟨s(u, v), fun h ↦ huv (Sym2.mk_isDiag_iff.mp h)⟩ ↔
      Twist.splitKlein (X u - X v) = 0 := by
  rfl

omit [DecidableEq V] in
/-- Common translation of every twist leaves all edge differences unchanged. -/
theorem isNullDifferenceConfiguration_add_common
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : IsNullDifferenceConfiguration F X) (A : Twist k) :
    IsNullDifferenceConfiguration F (fun v ↦ X v + A) := by
  rintro ⟨z, hz⟩ he
  have hNull := hX ⟨z, hz⟩ he
  unfold IsNullOnEdge at hNull ⊢
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.lift_mk] at hNull ⊢
      rw [show (X u + A) - (X v + A) = X u - X v by abel]
      exact hNull

omit [DecidableEq V] in
/-- Common scaling preserves the null equations, including at scale zero. -/
theorem isNullDifferenceConfiguration_smul
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : IsNullDifferenceConfiguration F X) (a : k) :
    IsNullDifferenceConfiguration F (fun v ↦ a • X v) := by
  rintro ⟨z, hz⟩ he
  have hNull := hX ⟨z, hz⟩ he
  unfold IsNullOnEdge at hNull ⊢
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.lift_mk] at hNull ⊢
      rw [← smul_sub, Twist.splitKlein_smul, hNull, mul_zero]

omit [DecidableEq V] in
theorem isDistinctConfiguration_add_common
    {X : V → Twist k} (hX : IsDistinctConfiguration X) (A : Twist k) :
    IsDistinctConfiguration (fun v ↦ X v + A) := by
  intro u v huv
  apply hX
  exact add_right_cancel huv

omit [DecidableEq V] in
theorem isDistinctConfiguration_smul
    {K : Type*} [Field K] {X : V → Twist K}
    (hX : IsDistinctConfiguration X) {a : K} (ha : a ≠ 0) :
    IsDistinctConfiguration (fun v ↦ a • X v) := by
  intro u v huv
  apply hX
  have h := congrArg (fun Z : Twist K ↦ a⁻¹ • Z) huv
  simpa [smul_smul, ha] using h

omit [DecidableEq V] in
theorem inNullCellule_add_common
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : InNullCellule F X) (A : Twist k) :
    InNullCellule F (fun v ↦ X v + A) :=
  ⟨isDistinctConfiguration_add_common hX.1 A,
    isNullDifferenceConfiguration_add_common hX.2 A⟩

omit [DecidableEq V] in
theorem inNullCellule_smul
    {K : Type*} [Field K] {F : SimpleEdgeSet V} {X : V → Twist K}
    (hX : InNullCellule F X) {a : K} (ha : a ≠ 0) :
    InNullCellule F (fun v ↦ a • X v) :=
  ⟨isDistinctConfiguration_smul hX.1 ha,
    isNullDifferenceConfiguration_smul hX.2 a⟩

end RB31E2E
