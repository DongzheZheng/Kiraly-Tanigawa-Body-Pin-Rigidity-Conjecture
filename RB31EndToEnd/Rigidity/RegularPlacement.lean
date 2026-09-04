import RB31EndToEnd.Rigidity.GraphNecessity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Topology.Baire.Lemmas

/-!
# Regular and generic placements

For a fixed graph, a placement is regular when its realized rigidity rank is
the maximum rank attained by that graph.  The regular placements form an open
dense set.  Since a finite vertex type has only finitely many simple graphs,
there are placements that are regular for every graph simultaneously.
-/

namespace RB31E2E
namespace BarJoint

open Module
open scoped BigOperators

/-- A placement is regular for `G` when the rigidity operator has its maximum
attained rank there. -/
def IsRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : Prop :=
  rigidityRank G p = genericRigidityRank G d

/-- A placement is generic when it is regular for every simple graph on the
same labelled vertex set. -/
def IsGenericPlacement {V : Type} [Fintype V] {d : ℕ}
    (p : Placement V d) : Prop :=
  ∀ G : SimpleGraph V, IsRegularPlacement G p

/-- The regular placements of a fixed graph form an open set. -/
theorem isOpen_isRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) :
    IsOpen {p : Placement V d | IsRegularPlacement G p} := by
  have hopen :=
    isOpen_setOf_le_rigidityRank (d := d) G (genericRigidityRank G d)
  convert hopen using 1
  ext p
  simp only [Set.mem_setOf_eq, IsRegularPlacement]
  constructor
  · intro h
    exact h.ge
  · intro h
    exact le_antisymm (rigidityRank_le_genericRigidityRank G d p) h

/-- The regular placements of a fixed graph are dense. -/
theorem dense_isRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) :
    Dense {p : Placement V d | IsRegularPlacement G p} := by
  classical
  let r := genericRigidityRank G d
  obtain ⟨w, hw⟩ := exists_rigidityRank_eq_genericRigidityRank G d
  have hfin : Module.finrank ℝ
      (LinearMap.range (rigidityOperator G w)) = r := by
    simpa [rigidityRank, r] using hw
  let b : Basis (Fin r) ℝ (LinearMap.range (rigidityOperator G w)) :=
    Module.finBasisOfFinrankEq ℝ _ hfin
  obtain ⟨lift, hlift⟩ :=
    (rigidityOperator G w).rangeRestrict.exists_rightInverse_of_surjective
      (rigidityOperator G w).range_rangeRestrict
  let U₀ : (Fin r → ℝ) →ₗ[ℝ] Velocity V d :=
    lift.comp b.equivFun.symm.toLinearMap
  let T₀ : (Fin r → ℝ) →ₗ[ℝ] (V × V → ℝ) :=
    (LinearMap.range (rigidityOperator G w)).subtype.comp
      b.equivFun.symm.toLinearMap
  have hRwU : (rigidityOperator G w).comp U₀ = T₀ := by
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun hlift (b.equivFun.symm a)
    exact congrArg Subtype.val h
  have hT₀inj : Function.Injective T₀ := by
    intro x y hxy
    apply b.equivFun.symm.injective
    exact Subtype.ext hxy
  have hT₀ker : LinearMap.ker T₀ = ⊥ :=
    LinearMap.ker_eq_bot.mpr hT₀inj
  let φ : (V × V → ℝ) →ₗ[ℝ] (Fin r → ℝ) := T₀.leftInverse
  have hφT₀ : φ.comp T₀ = LinearMap.id := by
    exact T₀.leftInverse_comp_of_inj hT₀ker

  refine dense_iff_inter_open.mpr ?_
  intro O hO ⟨p, hpO⟩
  let q : ℝ → Placement V d := fun t ↦ p + t • (w - p)
  have hq_cont : Continuous q :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hq_zero : q 0 = p := by simp [q]
  have hq_preimage_open : IsOpen (q ⁻¹' O) := hO.preimage hq_cont
  have hzero_preimage : (0 : ℝ) ∈ q ⁻¹' O := by
    simpa [hq_zero] using hpO
  have hpreimage_nhds : q ⁻¹' O ∈ nhds (0 : ℝ) :=
    hq_preimage_open.mem_nhds hzero_preimage
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hpreimage_nhds

  let A₀ : Module.End ℝ (Fin r → ℝ) :=
    φ.comp ((rigidityOperator G p).comp U₀)
  let A₁ : Module.End ℝ (Fin r → ℝ) :=
    φ.comp ((rigidityOperator G (w - p)).comp U₀)
  let e : Basis (Fin r) ℝ (Fin r → ℝ) := Pi.basisFun ℝ (Fin r)
  let M₀ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₀
  let M₁ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₁
  let P : Polynomial ℝ :=
    Matrix.det
      ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C +
        M₀.map Polynomial.C)

  have hoperator_line (t : ℝ) :
      rigidityOperator G (q t) =
        rigidityOperator G p + t • rigidityOperator G (w - p) := by
    change (rigidityOperatorLinearInPlacement G) (p + t • (w - p)) =
      (rigidityOperatorLinearInPlacement G) p +
        t • (rigidityOperatorLinearInPlacement G) (w - p)
    rw [map_add, map_smul]
  have hA_line (t : ℝ) :
      A₀ + t • A₁ = φ.comp ((rigidityOperator G (q t)).comp U₀) := by
    rw [hoperator_line]
    ext a
    simp [A₀, A₁]
  have hP_eval (t : ℝ) :
      P.eval t = LinearMap.det (A₀ + t • A₁) := by
    dsimp only [P]
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    rw [← LinearMap.det_toMatrix e]
    congr 1
    ext i j
    simp [M₀, M₁]
    ring
  have hA_one : A₀ + (1 : ℝ) • A₁ = LinearMap.id := by
    rw [hA_line 1, show q 1 = w by simp [q], hRwU, hφT₀]
  have hP_one : P.eval 1 = 1 := by
    rw [hP_eval, hA_one]
    simp
  have hP_ne : P ≠ 0 := by
    intro hP
    simp [hP] at hP_one

  let Z : Set ℝ := {t | Polynomial.IsRoot P t}
  have hZfinite : Z.Finite := by
    simpa [Z] using Polynomial.finite_setOf_isRoot hP_ne
  have hintervalInfinite : (Set.Ioo (0 : ℝ) ε).Infinite :=
    Set.Ioo_infinite hεpos
  have hnotSubset : ¬ Set.Ioo (0 : ℝ) ε ⊆ Z := by
    intro hsubset
    exact hintervalInfinite (hZfinite.subset hsubset)
  obtain ⟨t, htInterval, htNotRoot⟩ := Set.not_subset.mp hnotSubset
  have hP_t : P.eval t ≠ 0 := by
    simpa [Z, Polynomial.IsRoot] using htNotRoot
  have hA_t_det : LinearMap.det (A₀ + t • A₁) ≠ 0 := by
    simpa [hP_eval t] using hP_t
  have hA_t_ker : LinearMap.ker (A₀ + t • A₁) = ⊥ := by
    by_contra hker
    exact hA_t_det (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  have hA_t_inj : Function.Injective (A₀ + t • A₁) :=
    LinearMap.ker_eq_bot.mp hA_t_ker
  let RqU : (Fin r → ℝ) →ₗ[ℝ] (V × V → ℝ) :=
    (rigidityOperator G (q t)).comp U₀
  have hRqU_inj : Function.Injective RqU := by
    intro x y hxy
    apply hA_t_inj
    rw [hA_line]
    exact congrArg φ hxy
  have hrank_lower : r ≤ rigidityRank G (q t) := by
    rw [rigidityRank]
    calc
      r = Module.finrank ℝ (Fin r → ℝ) := by simp
      _ = Module.finrank ℝ (LinearMap.range RqU) :=
        (LinearMap.finrank_range_of_inj hRqU_inj).symm
      _ ≤ Module.finrank ℝ (LinearMap.range (rigidityOperator G (q t))) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hq_regular : IsRegularPlacement G (q t) := by
    exact le_antisymm (rigidityRank_le_genericRigidityRank G d (q t)) hrank_lower
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos htInterval.1]
    exact htInterval.2
  exact ⟨q t, hball ht_ball, hq_regular⟩

/-- Placements regular for every graph form an open set. -/
theorem isOpen_isGenericPlacement {V : Type} [Fintype V] {d : ℕ} :
    IsOpen {p : Placement V d | IsGenericPlacement p} := by
  rw [show {p : Placement V d | IsGenericPlacement p} =
      ⋂ G : SimpleGraph V, {p : Placement V d | IsRegularPlacement G p} by
    ext p
    simp [IsGenericPlacement]]
  exact isOpen_iInter_of_finite fun G ↦ isOpen_isRegularPlacement G

/-- Placements regular for every graph are dense. -/
theorem dense_isGenericPlacement {V : Type} [Fintype V] {d : ℕ} :
    Dense {p : Placement V d | IsGenericPlacement p} := by
  rw [show {p : Placement V d | IsGenericPlacement p} =
      ⋂ G : SimpleGraph V, {p : Placement V d | IsRegularPlacement G p} by
    ext p
    simp [IsGenericPlacement]]
  exact dense_iInter_of_isOpen
    (fun G ↦ isOpen_isRegularPlacement G)
    (fun G ↦ dense_isRegularPlacement G)

/-- A finite labelled vertex set admits a placement regular for every simple
graph on that set. -/
theorem exists_isGenericPlacement {V : Type} [Fintype V] (d : ℕ) :
    ∃ p : Placement V d, IsGenericPlacement p := by
  have hdense := dense_isGenericPlacement (V := V) (d := d)
  obtain ⟨p, hp, -⟩ := hdense.exists_mem_open isOpen_univ
    (Set.univ_nonempty : (Set.univ : Set (Placement V d)).Nonempty)
  exact ⟨p, hp⟩

end BarJoint
end RB31E2E
