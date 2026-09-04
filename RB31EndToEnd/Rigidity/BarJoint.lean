import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-!
# Real bar--joint infinitesimal rigidity

This file gives the actual linearized bar constraints over `ℝ`.  Generic rank
is defined as the attained maximum rank among all placements, not as a desired
combinatorial formula.  A graph is generically rigid when its maximum rank
agrees with the complete graph on the same vertex type; this convention also
handles vertex sets of size smaller than the ambient affine dimension.
-/

namespace RB31E2E
namespace BarJoint

open scoped BigOperators

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

theorem edgeConstraint_comm {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) :
    edgeConstraint p u v w = edgeConstraint p u w v := by
  apply Finset.sum_congr rfl
  intro i _
  ring

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

@[simp] theorem edgeFunctional_apply {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) :
    edgeFunctional p v w u = edgeConstraint p u v w :=
  rfl

/--
The real rigidity operator.  Its target uses all ordered vertex pairs; nonedges
and diagonal pairs receive zero.  Doubling an undirected row does not alter
rank, while this fixed target makes ranks of different graphs directly
comparable.
-/
noncomputable def rigidityOperator {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    Velocity V d →ₗ[ℝ] (V × V → ℝ) := by
  classical
  exact LinearMap.pi fun vw ↦
    if G.Adj vw.1 vw.2 then edgeFunctional p vw.1 vw.2 else 0

@[simp] theorem rigidityOperator_apply_of_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) (v w : V)
    (h : G.Adj v w) :
    rigidityOperator G p u (v, w) = edgeConstraint p u v w := by
  classical
  simp [rigidityOperator, h]

@[simp] theorem rigidityOperator_apply_of_not_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) (v w : V)
    (h : ¬ G.Adj v w) :
    rigidityOperator G p u (v, w) = 0 := by
  classical
  simp [rigidityOperator, h]

/-- A velocity is an infinitesimal motion precisely when every bar row vanishes. -/
def IsInfinitesimalMotion {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) : Prop :=
  u ∈ (rigidityOperator G p).ker

theorem isInfinitesimalMotion_iff {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) :
    IsInfinitesimalMotion G p u ↔
      ∀ v w : V, G.Adj v w → edgeConstraint p u v w = 0 := by
  classical
  constructor
  · intro hu v w hvw
    have hZero : rigidityOperator G p u = 0 := LinearMap.mem_ker.mp hu
    have hAt := congrFun hZero (v, w)
    simpa [rigidityOperator, hvw] using hAt
  · intro hu
    rw [IsInfinitesimalMotion, LinearMap.mem_ker]
    funext vw
    by_cases h : G.Adj vw.1 vw.2
    · simpa [rigidityOperator, h] using hu vw.1 vw.2 h
    · simp [rigidityOperator, h]

/-- Every constant velocity field is a translational infinitesimal motion. -/
theorem translation_isInfinitesimalMotion {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (a : Point d) :
    IsInfinitesimalMotion G p (fun _ ↦ a) := by
  rw [isInfinitesimalMotion_iff]
  intro v w _
  simp [edgeConstraint]

theorem finrank_velocity {V : Type} [Fintype V] (d : ℕ) :
    Module.finrank ℝ (Velocity V d) = Fintype.card V * d := by
  rw [Module.finrank_pi_fintype]
  simp

theorem rigidityOperator_bot {V : Type} {d : ℕ} (p : Placement V d) :
    rigidityOperator (⊥ : SimpleGraph V) p = 0 := by
  classical
  ext u vw
  simp [rigidityOperator]

/-- The rank of the actual rigidity operator at one placement. -/
noncomputable def rigidityRank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : ℕ :=
  Module.finrank ℝ (LinearMap.range (rigidityOperator G p))

@[simp] theorem rigidityRank_bot {V : Type} [Fintype V] {d : ℕ}
    (p : Placement V d) :
    rigidityRank (⊥ : SimpleGraph V) p = 0 := by
  rw [rigidityRank, rigidityOperator_bot, LinearMap.range_zero]
  simp

theorem rigidityRank_le_velocityFinrank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    rigidityRank G p ≤ Module.finrank ℝ (Velocity V d) := by
  exact LinearMap.finrank_range_le (rigidityOperator G p)

/-- The proposition that a specified operator rank occurs at a real placement. -/
def RankIsAttained {V : Type} [Fintype V] (G : SimpleGraph V) (d r : ℕ) : Prop :=
  ∃ p : Placement V d, rigidityRank G p = r

/--
The generic rigidity rank, defined as the greatest rank actually attained by a
real placement.  The search bound is the dimension of the velocity space, and
`rigidityRank_le_velocityFinrank` proves that no placement is omitted.
-/
noncomputable def genericRigidityRank {V : Type} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (RankIsAttained G d)
    (Module.finrank ℝ (Velocity V d))

theorem rigidityRank_le_genericRigidityRank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (p : Placement V d) :
    rigidityRank G p ≤ genericRigidityRank G d := by
  classical
  simpa [genericRigidityRank] using
    (Nat.le_findGreatest (P := RankIsAttained G d)
      (rigidityRank_le_velocityFinrank G p) (show RankIsAttained G d (rigidityRank G p) from ⟨p, rfl⟩))

theorem genericRigidityRank_le_velocityFinrank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    genericRigidityRank G d ≤ Module.finrank ℝ (Velocity V d) := by
  classical
  simpa [genericRigidityRank] using
    (Nat.findGreatest_le (P := RankIsAttained G d)
      (Module.finrank ℝ (Velocity V d)))

/-- The maximum rank is attained by at least one real placement. -/
theorem exists_rigidityRank_eq_genericRigidityRank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    ∃ p : Placement V d, rigidityRank G p = genericRigidityRank G d := by
  classical
  let p₀ : Placement V d := 0
  have h := Nat.findGreatest_spec (P := RankIsAttained G d)
    (rigidityRank_le_velocityFinrank G p₀)
    (show RankIsAttained G d (rigidityRank G p₀) from ⟨p₀, rfl⟩)
  simpa [genericRigidityRank, RankIsAttained] using h

@[simp] theorem genericRigidityRank_bot {V : Type} [Fintype V] (d : ℕ) :
    genericRigidityRank (⊥ : SimpleGraph V) d = 0 := by
  rcases exists_rigidityRank_eq_genericRigidityRank (⊥ : SimpleGraph V) d with ⟨p, hp⟩
  rw [← hp, rigidityRank_bot]

theorem eq_bot_of_subsingleton {V : Type} [Subsingleton V] (G : SimpleGraph V) :
    G = ⊥ := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  constructor
  · intro h
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact (G.loopless.irrefl v h).elim
  · intro h
    exact (SimpleGraph.bot_adj v w).mp h |>.elim

/-- On zero or one vertex, every simple graph has actual generic rank zero. -/
theorem genericRigidityRank_eq_zero_of_subsingleton
    {V : Type} [Fintype V] [Subsingleton V] (G : SimpleGraph V) (d : ℕ) :
    genericRigidityRank G d = 0 := by
  rw [eq_bot_of_subsingleton G, genericRigidityRank_bot]

/--
Maximum-rank semantics of generic infinitesimal rigidity.  Comparison with the
complete graph is valid uniformly, including when `Fintype.card V < d + 1`.
-/
def IsGenericallyRigidInDimension {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  genericRigidityRank G d =
    genericRigidityRank (SimpleGraph.completeGraph V) d

/-- The dimension-three specialization used by the body--pin theorem. -/
def IsGenericallyRigidInR3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsGenericallyRigidInDimension G 3

@[simp] theorem completeGraph_isGenericallyRigidInDimension
    (V : Type) [Fintype V] (d : ℕ) :
    IsGenericallyRigidInDimension (SimpleGraph.completeGraph V) d :=
  rfl

@[simp] theorem completeGraph_isGenericallyRigidInR3
    (V : Type) [Fintype V] :
    IsGenericallyRigidInR3 (SimpleGraph.completeGraph V) :=
  rfl

/-- The classical complete-framework rank target, including small `n`. -/
def completeFrameworkRankTarget (d n : ℕ) : ℕ :=
  if n ≤ d + 1 then Nat.choose n 2
  else d * n - Nat.choose (d + 1) 2

@[simp] theorem completeFrameworkRankTarget_three_zero :
    completeFrameworkRankTarget 3 0 = 0 := by decide

@[simp] theorem completeFrameworkRankTarget_three_one :
    completeFrameworkRankTarget 3 1 = 0 := by decide

@[simp] theorem completeFrameworkRankTarget_three_two :
    completeFrameworkRankTarget 3 2 = 1 := by decide

@[simp] theorem completeFrameworkRankTarget_three_three :
    completeFrameworkRankTarget 3 3 = 3 := by decide

@[simp] theorem completeFrameworkRankTarget_three_four :
    completeFrameworkRankTarget 3 4 = 6 := by decide

end BarJoint
end RB31E2E
