import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-!
# Three-dimensional body--pin rigidity: statement surface

This file is the small, Mathlib-only statement surface used by
`leanprover/comparator`.  Its final `sorry` is the deliberate challenge hole;
the production formalization contains no proof placeholders.
-/

namespace RB31E2E

/-- The capped rank contribution of a bundle of body--pin occurrences. -/
def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

/-- A finite loopless body--pin multigraph with occurrence-indexed pins. -/
structure BodyPinIncidence where
  Body : Type
  Pin : Type
  bodyFinite : Fintype Body
  pinFinite : Fintype Pin
  bodyDecidableEq : DecidableEq Body
  pinDecidableEq : DecidableEq Pin
  left : Pin → Body
  right : Pin → Body
  loopless : ∀ e, left e ≠ right e

attribute [instance] BodyPinIncidence.bodyFinite
attribute [instance] BodyPinIncidence.pinFinite
attribute [instance] BodyPinIncidence.bodyDecidableEq
attribute [instance] BodyPinIncidence.pinDecidableEq

/-- Multiplicity indexed by an unordered pair of partition blocks. -/
def BodyPinIncidence.unorderedBundleMultiplicity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (b : Sym2 (Fin t)) : ℕ :=
  (Finset.univ.filter fun e => s(π (H.left e), π (H.right e)) = b).card

/-- The capacity sum over unordered pairs of distinct partition blocks. -/
def BodyPinIncidence.partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  ∑ b ∈ (⊤ : SimpleGraph (Fin t)).edgeFinset,
    pinCapacity (H.unorderedBundleMultiplicity π b)

/-- The body--pin partition condition. -/
def BodyPinIncidence.PartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    6 * (t - 1) ≤ H.partitionCapacity π

namespace BarJoint

/-- A point in real coordinate dimension `d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- A placement of the vertices in real coordinate dimension `d`. -/
abbrev Placement (V : Type) (d : ℕ) := V → Point d

/-- An infinitesimal velocity assignment. -/
abbrev Velocity (V : Type) (d : ℕ) := V → Point d

/-- The linearized squared-length constraint for the ordered pair `(v,w)`. -/
def edgeConstraint {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) : ℝ :=
  ∑ i : Fin d, (p v i - p w i) * (u v i - u w i)

/-- One bar constraint as a real linear functional of the velocity. -/
def edgeFunctional {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) : Velocity V d →ₗ[ℝ] ℝ where
  toFun u := edgeConstraint p u v w
  map_add' u z := by
    simp only [edgeConstraint, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c u := by
    simp only [edgeConstraint, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The real rigidity operator, with a fixed ordered-pair codomain. -/
noncomputable def rigidityOperator {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    Velocity V d →ₗ[ℝ] (V × V → ℝ) := by
  classical
  exact LinearMap.pi fun vw ↦
    if G.Adj vw.1 vw.2 then edgeFunctional p vw.1 vw.2 else 0

/-- The rank of the rigidity operator at one placement. -/
noncomputable def rigidityRank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : ℕ :=
  Module.finrank ℝ (LinearMap.range (rigidityOperator G p))

/-- The proposition that a specified rigidity rank is attained. -/
def RankIsAttained {V : Type} [Fintype V] (G : SimpleGraph V) (d r : ℕ) : Prop :=
  ∃ p : Placement V d, rigidityRank G p = r

/-- The maximum rank attained by a real placement. -/
noncomputable def genericRigidityRank {V : Type} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (RankIsAttained G d)
    (Module.finrank ℝ (Velocity V d))

/-- Maximum-rank generic rigidity in coordinate dimension `d`. -/
def IsGenericallyRigidInDimension {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  genericRigidityRank G d =
    genericRigidityRank (SimpleGraph.completeGraph V) d

/-- Maximum-rank generic rigidity in three dimensions. -/
def IsGenericallyRigidInR3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsGenericallyRigidInDimension G 3

end BarJoint

namespace BodyPinIncidence

/-- Vertices of the expanded bar--joint graph. -/
abbrev BPVertex (H : BodyPinIncidence) (extra : H.Body → ℕ) :=
  H.Pin ⊕ ((b : H.Body) × Fin (4 + extra b))

/-- Incidence of an expanded graph vertex with a body clique. -/
def VertexBelongsToBody (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) : H.BPVertex extra → Prop
  | Sum.inl e => H.left e = b ∨ H.right e = b
  | Sum.inr x => x.1 = b

/-- The complete simple graph supported on the vertices belonging to one body. -/
def bodyClique (H : BodyPinIncidence) (extra : H.Body → ℕ) (b : H.Body) :
    SimpleGraph (H.BPVertex extra) where
  Adj v w := v ≠ w ∧
    H.VertexBelongsToBody extra b v ∧ H.VertexBelongsToBody extra b w
  symm v w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

/-- The expanded body--pin graph, the union of its body cliques. -/
def bodyPinGraph (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    SimpleGraph (H.BPVertex extra) :=
  ⨆ b : H.Body, H.bodyClique extra b

/-- Real maximum-rank generic rigidity of the expanded graph. -/
def GenericallyRigidInR3 (H : BodyPinIncidence) (extra : H.Body → ℕ) : Prop :=
  BarJoint.IsGenericallyRigidInR3 (H.bodyPinGraph extra)

end BodyPinIncidence

/-- For every finite loopless body--pin multigraph and every permitted number
of private body vertices, the partition condition is equivalent to
maximum-rank generic rigidity of the expanded graph in `ℝ³`. -/
def EndToEndBodyPinStatement : Prop :=
  ∀ (H : BodyPinIncidence) (extra : H.Body → ℕ),
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition

/-- Comparator challenge for the three-dimensional body--pin partition theorem. -/
theorem endToEndBodyPinStatement : EndToEndBodyPinStatement := by
  sorry

end RB31E2E
