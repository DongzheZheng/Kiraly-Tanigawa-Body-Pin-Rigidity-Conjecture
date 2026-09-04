import RB31EndToEnd.Rigidity.LocalRigidity
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Congruence and rigidity rank

Pairwise-congruent finite Euclidean placements have rigidity operators of the
same rank.  The proof constructs an ambient Euclidean isometry from equality
of the finite distance data and transports velocities through that isometry.
-/

namespace RB31E2E.BarJoint

open scoped BigOperators Topology

variable {V : Type} {d : ℕ}

private theorem centered_inner_eq_of_dist_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : V → E) (v₀ v w : V)
    (h : ∀ x y, dist (a x) (a y) = dist (b x) (b y)) :
    inner ℝ (a v - a v₀) (a w - a v₀) =
      inner ℝ (b v - b v₀) (b w - b v₀) := by
  have hv : ‖a v - a v₀‖ = ‖b v - b v₀‖ := by
    simpa [dist_eq_norm] using h v v₀
  have hw : ‖a w - a v₀‖ = ‖b w - b v₀‖ := by
    simpa [dist_eq_norm] using h w v₀
  have hvw : ‖(a v - a v₀) - (a w - a v₀)‖ =
      ‖(b v - b v₀) - (b w - b v₀)‖ := by
    simpa [dist_eq_norm] using h v w
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    hv, hw, hvw]

private theorem inner_linearCombination_eq_of_gram_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : V → E)
    (h : ∀ i j, inner ℝ (a i) (a j) = inner ℝ (b i) (b j))
    (x y : V →₀ ℝ) :
    inner ℝ (Finsupp.linearCombination ℝ a x)
        (Finsupp.linearCombination ℝ a y) =
      inner ℝ (Finsupp.linearCombination ℝ b x)
        (Finsupp.linearCombination ℝ b y) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum,
    sum_inner, real_inner_smul_left, real_inner_smul_right, h]

private theorem ker_le_of_inner_eq
    {F E : Type*} [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : F →ₗ[ℝ] E)
    (hinner : ∀ x y, inner ℝ (A x) (A y) = inner ℝ (B x) (B y)) :
    LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hself := hinner x x
    rw [hx, inner_zero_left] at hself
    exact inner_self_eq_zero.mp hself.symm

private theorem exists_range_linearIsometry
    {F E : Type*} [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : F →ₗ[ℝ] E)
    (hinner : ∀ x y, inner ℝ (A x) (A y) = inner ℝ (B x) (B y)) :
    ∃ J : LinearMap.range A →ₗᵢ[ℝ] E,
      ∀ x, J ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
  classical
  have hker : LinearMap.ker A ≤ LinearMap.ker B :=
    ker_le_of_inner_eq A B hinner
  obtain ⟨lift, hlift⟩ :=
    A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  have hlift_apply (x : LinearMap.range A) : A (lift x) = x := by
    have hx := LinearMap.congr_fun hlift x
    exact congrArg Subtype.val hx
  let L : LinearMap.range A →ₗ[ℝ] E := B.comp lift
  have hL (x : F) :
      L ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    have hzero : A (lift ⟨A x, LinearMap.mem_range_self A x⟩ - x) = 0 := by
      rw [map_sub, hlift_apply]
      simp
    have hmem : lift ⟨A x, LinearMap.mem_range_self A x⟩ - x ∈
        LinearMap.ker A := LinearMap.mem_ker.mpr hzero
    have hBzero := LinearMap.mem_ker.mp (hker hmem)
    change B (lift ⟨A x, LinearMap.mem_range_self A x⟩) = B x
    rw [map_sub] at hBzero
    exact sub_eq_zero.mp hBzero
  have hLinner (x y : LinearMap.range A) :
      inner ℝ (L x) (L y) = inner ℝ x y := by
    change inner ℝ (B (lift x)) (B (lift y)) = inner ℝ (x : E) (y : E)
    rw [← hinner, hlift_apply, hlift_apply]
  let J : LinearMap.range A →ₗᵢ[ℝ] E := L.isometryOfInner hLinner
  exact ⟨J, hL⟩

private theorem exists_linearIsometry_of_gram_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a b : V → E)
    (h : ∀ i j, inner ℝ (a i) (a j) = inner ℝ (b i) (b j)) :
    ∃ Q : E →ₗᵢ[ℝ] E, ∀ i, Q (a i) = b i := by
  classical
  let A : (V →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ a
  let B : (V →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ b
  have hinner (x y : V →₀ ℝ) :
      inner ℝ (A x) (A y) = inner ℝ (B x) (B y) :=
    inner_linearCombination_eq_of_gram_eq a b h x y
  obtain ⟨J, hJ⟩ := exists_range_linearIsometry A B hinner
  let Q : E →ₗᵢ[ℝ] E := J.extend
  refine ⟨Q, ?_⟩
  intro i
  let eᵢ : V →₀ ℝ := Finsupp.single i 1
  have hAe : A eᵢ = a i := by simp [A, eᵢ]
  have hBe : B eᵢ = b i := by simp [B, eᵢ]
  calc
    Q (a i) = Q (A eᵢ) := by rw [hAe]
    _ = J ⟨A eᵢ, LinearMap.mem_range_self A eᵢ⟩ := by
      change J.extend
          (⟨A eᵢ, LinearMap.mem_range_self A eᵢ⟩ : LinearMap.range A) =
        J ⟨A eᵢ, LinearMap.mem_range_self A eᵢ⟩
      exact LinearIsometry.extend_apply J _
    _ = B eᵢ := hJ eᵢ
    _ = b i := hBe

private theorem edgeConstraint_eq_euclidean_inner
    (p : Placement V d) (u : Velocity V d) (v w : V) :
    edgeConstraint p u v w =
      inner ℝ
        (toEuclideanPoint (p v) - toEuclideanPoint (p w))
        (toEuclideanPoint (u v) - toEuclideanPoint (u w)) := by
  have hscalar (x y : ℝ) : inner ℝ x y = x * y := by
    change y * x = x * y
    ring
  simp [edgeConstraint, toEuclideanPoint, PiLp.inner_apply, hscalar]

private theorem exists_euclidean_linearIsometry_of_isCongruent
    [Nonempty V] (p q : Placement V d) (h : IsCongruent p q) :
    ∃ Q : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ v w,
        Q (toEuclideanPoint (p v) - toEuclideanPoint (p w)) =
          toEuclideanPoint (q v) - toEuclideanPoint (q w) := by
  let v₀ : V := Classical.choice inferInstance
  let a : V → EuclideanSpace ℝ (Fin d) :=
    fun v ↦ toEuclideanPoint (p v) - toEuclideanPoint (p v₀)
  let b : V → EuclideanSpace ℝ (Fin d) :=
    fun v ↦ toEuclideanPoint (q v) - toEuclideanPoint (q v₀)
  have hgram (v w : V) : inner ℝ (a v) (a w) = inner ℝ (b v) (b w) := by
    exact centered_inner_eq_of_dist_eq
      (toEuclideanPlacement p) (toEuclideanPlacement q) v₀ v w h
  obtain ⟨Q, hQ⟩ := exists_linearIsometry_of_gram_eq a b hgram
  refine ⟨Q, ?_⟩
  intro v w
  calc
    Q (toEuclideanPoint (p v) - toEuclideanPoint (p w)) =
        Q (a v - a w) := by
          congr 1
          simp only [a]
          abel
    _ = Q (a v) - Q (a w) := map_sub Q (a v) (a w)
    _ = b v - b w := by rw [hQ, hQ]
    _ = toEuclideanPoint (q v) - toEuclideanPoint (q w) := by
      simp only [b]
      abel

/-- Congruent labelled placements have rigidity operators of the same rank. -/
theorem rigidityRank_eq_of_isCongruent [Fintype V]
    (G : SimpleGraph V) (p q : Placement V d) (h : IsCongruent p q) :
    rigidityRank G p = rigidityRank G q := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      have hG : G = ⊥ := Subsingleton.elim G ⊥
      simp [hG]
  | inr hV =>
      letI := hV
      obtain ⟨Q, hQ⟩ := exists_euclidean_linearIsometry_of_isCongruent p q h
      have hQsurj : Function.Surjective Q :=
        LinearMap.surjective_of_injective Q.injective
      let Qe : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
        LinearIsometryEquiv.ofSurjective Q hQsurj
      let U : Velocity V d ≃ₗ[ℝ] Velocity V d :=
        (placementEuclideanEquiv (V := V) (d := d)).toLinearEquiv.trans
          ((LinearEquiv.piCongrRight fun _ : V ↦ Qe.toLinearEquiv).trans
            (placementEuclideanEquiv (V := V) (d := d)).symm.toLinearEquiv)
      have hU (u : Velocity V d) (v : V) :
          toEuclideanPoint (U u v) = Q (toEuclideanPoint (u v)) := by
        rfl
      have hintertwine :
          (rigidityOperator G q).comp U.toLinearMap = rigidityOperator G p := by
        apply LinearMap.ext
        intro u
        funext vw
        rcases vw with ⟨v, w⟩
        change rigidityOperator G q (U u) (v, w) =
          rigidityOperator G p u (v, w)
        by_cases hadj : G.Adj v w
        · rw [rigidityOperator_apply_of_adj G q (U u) v w hadj,
            rigidityOperator_apply_of_adj G p u v w hadj,
            edgeConstraint_eq_euclidean_inner,
            edgeConstraint_eq_euclidean_inner]
          have hUsub :
              toEuclideanPoint (U u v) - toEuclideanPoint (U u w) =
                Q (toEuclideanPoint (u v) - toEuclideanPoint (u w)) := by
            rw [hU, hU, map_sub]
          rw [← hQ v w, hUsub, Q.inner_map_map]
        · rw [rigidityOperator_apply_of_not_adj G q (U u) v w hadj,
            rigidityOperator_apply_of_not_adj G p u v w hadj]
      unfold rigidityRank
      rw [← hintertwine]
      rw [LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr U.surjective)]

end RB31E2E.BarJoint
