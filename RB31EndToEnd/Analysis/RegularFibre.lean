import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Regular fibres of a maximum-rank map

This file isolates the analytic implication used in the passage from local
rigidity to infinitesimal rigidity.  At a point where a `C¹` map has maximum
rank, every vector in its derivative kernel is tangent to a curve in the
corresponding local level set.  Consequently, a second `C¹` map which is
locally constant on that level set annihilates the first kernel.

The proof uses the implicit function theorem after projecting the codomain
onto the range of the derivative at the base point.  Maximum rank makes the
discarded equations locally dependent on the projected ones.
-/

open Filter Set
open scoped Topology

namespace RB31E2E

noncomputable section

private theorem ker_eq_comp_of_finrank_range_eq
    {E F R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (A : E →L[ℝ] F) (P : F →L[ℝ] R)
    (hrank : Module.finrank ℝ (P.comp A).range =
      Module.finrank ℝ A.range) :
    A.ker = (P.comp A).ker := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    change P (A x) = 0
    rw [show A x = 0 from hx, map_zero]
  have hA := (A : E →ₗ[ℝ] F).finrank_range_add_finrank_ker
  have hPA := (P.comp A : E →ₗ[ℝ] R).finrank_range_add_finrank_ker
  omega

/-- At a maximum-rank point of a `C¹` map, a neighborhood in the level fibre
admits a finite-dimensional parametrized slice.  The slice is differentiable
at the origin, contains all tangent directions in the derivative kernel, and
is mapped to `f p` on a ball about the origin.

The maximum-rank hypothesis is stated using finite dimensions, so the result
also covers zero-dimensional source, target, and derivative range. -/
theorem exists_regular_fibre_slice
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {p : E}
    (hf : ContDiff ℝ 1 f)
    (hmax : ∀ q,
      Module.finrank ℝ (fderiv ℝ f q).range ≤
        Module.finrank ℝ (fderiv ℝ f p).range) :
    ∃ (s : ℕ) (ψ : (Fin s → ℝ) → E) (ε : ℝ),
      0 < ε ∧ ψ 0 = p ∧ DifferentiableAt ℝ ψ 0 ∧
      ContinuousOn ψ (Metric.ball 0 ε) ∧
      (∀ z ∈ Metric.ball 0 ε, f (ψ z) = f p) ∧
      (fderiv ℝ f p).ker ≤ (fderiv ℝ ψ 0).range := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F

  let A : E →L[ℝ] F := fderiv ℝ f p
  let projectionExists : A.range.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional A.range
  let P : F →L[ℝ] A.range := Classical.choose projectionExists
  have hP (y : A.range) : P y = y := Classical.choose_spec projectionExists y

  let r := Module.finrank ℝ A.range
  let coordinates : A.range ≃ₗ[ℝ] (Fin r → ℝ) :=
    LinearEquiv.ofFinrankEq A.range (Fin r → ℝ) (by simp [r])
  let PcoordLinear : F →ₗ[ℝ] (Fin r → ℝ) :=
    coordinates.toLinearMap.comp (P : F →ₗ[ℝ] A.range)
  let Pcoord : F →L[ℝ] (Fin r → ℝ) := PcoordLinear.toContinuousLinearMap

  let h : E → (Fin r → ℝ) := Pcoord ∘ f
  let Abar : E →L[ℝ] (Fin r → ℝ) := Pcoord.comp A
  have hh : ContDiff ℝ 1 h := Pcoord.contDiff.comp hf
  have hfderiv_h (q : E) : fderiv ℝ h q = Pcoord.comp (fderiv ℝ f q) := by
    exact (Pcoord.hasFDerivAt.comp q
      (hf.differentiable_one q).hasFDerivAt).fderiv
  have hAbar : fderiv ℝ h p = Abar := by
    simpa only [Abar, A] using hfderiv_h p

  have hAbar_surjective : Abar.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    let yrange : A.range := coordinates.symm y
    rcases yrange.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change coordinates (P (A x)) = y
    calc
      coordinates (P (A x)) = coordinates (P (yrange : F)) :=
        congrArg (fun z ↦ coordinates (P z)) hx
      _ = coordinates yrange := congrArg coordinates (hP yrange)
      _ = y := coordinates.apply_symm_apply y

  have hAbar_rank : Module.finrank ℝ Abar.range = r := by
    rw [hAbar_surjective]
    simp
  have hker_base : A.ker = Abar.ker :=
    ker_eq_comp_of_finrank_range_eq A Pcoord hAbar_rank

  have hdhp : HasStrictFDerivAt h Abar p :=
    (hh.hasStrictFDerivAt one_ne_zero).congr_fderiv hAbar

  have hlower : ∀ᶠ q in 𝓝 p,
      (r : Cardinal) ≤ (fderiv ℝ h q : E →ₗ[ℝ] (Fin r → ℝ)).rank := by
    have hp_rank : (r : Cardinal) ≤
        (fderiv ℝ h p : E →ₗ[ℝ] (Fin r → ℝ)).rank := by
      rw [hAbar]
      change (r : Cardinal) ≤ Module.rank ℝ Abar.range
      rw [← Module.finrank_eq_rank, hAbar_rank]
    exact (hh.continuous_fderiv one_ne_zero).continuousAt
      ((isOpen_setOf_nat_le_rank (E := E) (F := Fin r → ℝ) r).mem_nhds hp_rank)

  have hker_near : ∀ᶠ q in 𝓝 p,
      (fderiv ℝ f q).ker = (fderiv ℝ h q).ker := by
    filter_upwards [hlower] with q hq_lower
    let B : E →L[ℝ] F := fderiv ℝ f q
    let C : E →L[ℝ] (Fin r → ℝ) := fderiv ℝ h q
    have hC : C = Pcoord.comp B := by
      simpa only [B, C] using hfderiv_h q
    have hq_lower_nat : r ≤ Module.finrank ℝ C.range := by
      change (r : Cardinal) ≤ Module.rank ℝ C.range at hq_lower
      rw [← Module.finrank_eq_rank] at hq_lower
      exact_mod_cast hq_lower
    have hcomp : Module.finrank ℝ C.range ≤ Module.finrank ℝ B.range := by
      have hrank := LinearMap.lift_rank_comp_le_right
        (B : E →ₗ[ℝ] F) (Pcoord : F →ₗ[ℝ] (Fin r → ℝ))
      have hC_lin : (C : E →ₗ[ℝ] (Fin r → ℝ)) =
          (Pcoord : F →ₗ[ℝ] (Fin r → ℝ)).comp (B : E →ₗ[ℝ] F) :=
        congrArg ContinuousLinearMap.toLinearMap hC
      rw [← hC_lin] at hrank
      change Cardinal.lift (Module.rank ℝ C.range) ≤
        Cardinal.lift (Module.rank ℝ B.range) at hrank
      rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hrank
      have hfinite : Cardinal.lift
          (Module.finrank ℝ B.range : Cardinal) < Cardinal.aleph0 := by simp
      simpa using Cardinal.toNat_le_toNat hrank hfinite
    have hBmax : Module.finrank ℝ B.range ≤ r := by
      simpa only [B, A, r] using hmax q
    have hrange : Module.finrank ℝ C.range = Module.finrank ℝ B.range :=
      le_antisymm hcomp (hBmax.trans hq_lower_nat)
    change B.ker = C.ker
    have hrange' : Module.finrank ℝ (Pcoord.comp B).range =
        Module.finrank ℝ B.range := by
      rw [← hC]
      exact hrange
    rw [hC]
    exact ker_eq_comp_of_finrank_range_eq B Pcoord hrange'

  let kernelComplemented : Abar.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional Abar.ker
  let Q : E →L[ℝ] Abar.ker := Classical.choose kernelComplemented
  have hQ (z : Abar.ker) : Q z = z := Classical.choose_spec kernelComplemented z

  let s := Module.finrank ℝ Abar.ker
  let kernelCoordinates : Abar.ker ≃ₗ[ℝ] (Fin s → ℝ) :=
    LinearEquiv.ofFinrankEq Abar.ker (Fin s → ℝ) (by simp [s])
  let QcoordLinear : E →ₗ[ℝ] (Fin s → ℝ) :=
    kernelCoordinates.toLinearMap.comp (Q : E →ₗ[ℝ] Abar.ker)
  let Qcoord : E →L[ℝ] (Fin s → ℝ) := QcoordLinear.toContinuousLinearMap

  have hQcoord_surjective : Qcoord.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    let yker : Abar.ker := kernelCoordinates.symm y
    refine ⟨(yker : E), ?_⟩
    change kernelCoordinates (Q (yker : E)) = y
    rw [hQ yker]
    exact kernelCoordinates.apply_symm_apply y
  have hQcoord_ker : Qcoord.ker = Q.ker := by
    ext x
    constructor
    · intro hx
      change kernelCoordinates (Q x) = 0 at hx
      change Q x = 0
      apply kernelCoordinates.injective
      simpa only [map_zero] using hx
    · intro hx
      change Q x = 0 at hx
      change kernelCoordinates (Q x) = 0
      rw [hx, map_zero]
  have hker_complementary : IsCompl Abar.ker Qcoord.ker := by
    rw [hQcoord_ker]
    exact LinearMap.isCompl_of_proj (Classical.choose_spec kernelComplemented)

  let k : E → (Fin s → ℝ) := fun x ↦ Qcoord (x - p)
  have hkderiv : HasStrictFDerivAt k Qcoord p := by
    exact Qcoord.hasStrictFDerivAt.comp p
      ((hasStrictFDerivAt_id p).sub_const p)
  let Φ : ImplicitFunctionData ℝ E (Fin r → ℝ) (Fin s → ℝ) := {
    leftFun := h
    leftDeriv := Abar
    rightFun := k
    rightDeriv := Qcoord
    pt := p
    hasStrictFDerivAt_leftFun := hdhp
    hasStrictFDerivAt_rightFun := hkderiv
    range_leftDeriv := hAbar_surjective
    range_rightDeriv := hQcoord_surjective
    isCompl_ker := hker_complementary }
  let chart : OpenPartialHomeomorph E ((Fin r → ℝ) × (Fin s → ℝ)) :=
    Φ.toOpenPartialHomeomorph
  let ψ : (Fin s → ℝ) → E := fun z ↦ chart.symm (h p, z)
  let Dψ0 : (Fin s → ℝ) →L[ℝ] E := fderiv ℝ ψ 0

  have hψ0 : ψ 0 = p := by
    have hpSource : p ∈ chart.source := by
      simpa only [chart] using Φ.pt_mem_toOpenPartialHomeomorph_source
    have hleft := chart.leftInvOn hpSource
    simpa only [ψ, chart, Φ, ImplicitFunctionData.toOpenPartialHomeomorph_apply,
      k, sub_self, map_zero] using hleft
  have hψderiv0 : HasStrictFDerivAt ψ Dψ0 0 := by
    simpa only [ψ, chart, Dψ0, Φ, k, sub_self, map_zero,
      ImplicitFunctionData.implicitFunction_apply] using
      Φ.hasStrictFDerivAt_implicitFunction_fderiv
  have hψtendsto : Tendsto ψ (𝓝 0) (𝓝 p) := by
    rw [← hψ0]
    exact hψderiv0.continuousAt

  have hΦsmooth : ContDiff ℝ 1 Φ.prodFun := by
    change ContDiff ℝ 1
      (fun x ↦ (h x, Qcoord (x - p)))
    exact hh.prodMk
      (Qcoord.contDiff.comp (contDiff_id.sub contDiff_const))

  have hΦinv_near : ∀ᶠ q in 𝓝 p,
      (fderiv ℝ Φ.prodFun q).IsInvertible := by
    rcases Φ.isInvertible_fderiv_prodFun with ⟨L, hL⟩
    change ∀ᶠ q in 𝓝 p,
      fderiv ℝ Φ.prodFun q ∈
        Set.range ((↑) : (E ≃L[ℝ] ((Fin r → ℝ) × (Fin s → ℝ))) →
          E →L[ℝ] ((Fin r → ℝ) × (Fin s → ℝ)))
    apply (hΦsmooth.continuous_fderiv one_ne_zero).continuousAt
    rw [← hL]
    exact ContinuousLinearEquiv.nhds L

  have htarget_near : ∀ᶠ z in 𝓝 (0 : Fin s → ℝ),
      (h p, z) ∈ chart.target := by
    have htarget : (h p, (0 : Fin s → ℝ)) ∈ chart.target := by
      simpa only [chart, Φ, k, ImplicitFunctionData.prodFun_apply,
        sub_self, map_zero] using Φ.map_pt_mem_toOpenPartialHomeomorph_target
    exact (continuousAt_const.prodMk continuousAt_id)
      (chart.open_target.mem_nhds htarget)

  have hgood : ∀ᶠ z in 𝓝 (0 : Fin s → ℝ),
      (h p, z) ∈ chart.target ∧
      (fderiv ℝ Φ.prodFun (ψ z)).IsInvertible ∧
      (fderiv ℝ f (ψ z)).ker = (fderiv ℝ h (ψ z)).ker := by
    filter_upwards [htarget_near, hψtendsto hΦinv_near, hψtendsto hker_near]
      with z hzTarget hzInv hzKer
    exact ⟨hzTarget, hzInv, hzKer⟩

  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood

  have hslice_deriv (z : Fin s → ℝ) (hz : z ∈ Metric.ball 0 ε) :
      ∃ Dψ : (Fin s → ℝ) →L[ℝ] E,
        HasFDerivAt ψ Dψ z ∧ (fderiv ℝ f (ψ z)).comp Dψ = 0 := by
    rcases hball hz with ⟨hzTarget, hzInv, hzKer⟩
    let x : E := ψ z
    rcases hzInv with ⟨L, hL⟩
    have hchart_deriv : HasFDerivAt chart
        (L : E →L[ℝ] ((Fin r → ℝ) × (Fin s → ℝ))) x := by
      have hderiv : HasFDerivAt Φ.prodFun (fderiv ℝ Φ.prodFun x) x :=
        (hΦsmooth.differentiable_one x).hasFDerivAt
      rw [← hL] at hderiv
      simpa only [chart, Φ.toOpenPartialHomeomorph_coe] using hderiv
    have hinv_deriv : HasFDerivAt chart.symm
        (L.symm : ((Fin r → ℝ) × (Fin s → ℝ)) →L[ℝ] E) (h p, z) :=
      chart.hasFDerivAt_symm hzTarget hchart_deriv
    let Dψ : (Fin s → ℝ) →L[ℝ] E :=
      (L.symm : ((Fin r → ℝ) × (Fin s → ℝ)) →L[ℝ] E).comp
        (ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ))
    have hψderiv : HasFDerivAt ψ Dψ z := by
      have := hinv_deriv.comp z
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) (h p) z)
      simpa only [ψ, Dψ, Function.comp_def] using this

    have hloc : (fun w ↦ h (ψ w)) =ᶠ[𝓝 z] (fun _ ↦ h p) := by
      have hvert : Tendsto (fun w : Fin s → ℝ ↦ (h p, w))
          (𝓝 z) (𝓝 (h p, z)) := continuousAt_const.prodMk continuousAt_id
      filter_upwards [hvert (chart.eventually_right_inverse hzTarget)] with w hw
      have hw' := congrArg Prod.fst hw
      change h (chart.symm (h p, w)) = h p at hw'
      simpa only [ψ] using hw'
    have hhcomp : HasFDerivAt (fun w ↦ h (ψ w))
        ((fderiv ℝ h x).comp Dψ) z :=
      (hh.differentiable_one x).hasFDerivAt.comp z hψderiv
    have hhcomp_zero : (fderiv ℝ h x).comp Dψ = 0 :=
      hhcomp.unique (hasFDerivAt_zero_of_eventually_const (h p) hloc)
    have hfcomp_zero : (fderiv ℝ f x).comp Dψ = 0 := by
      ext v
      have hvh : fderiv ℝ h x (Dψ v) = 0 := by
        have hv := DFunLike.congr_fun hhcomp_zero v
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.zero_apply] using hv
      have hvker : Dψ v ∈ (fderiv ℝ f x).ker := by
        rw [hzKer]
        exact hvh
      exact hvker
    exact ⟨Dψ, hψderiv, hfcomp_zero⟩

  have hψ_continuous : ContinuousOn ψ (Metric.ball 0 ε) := by
    intro z hz
    rcases hslice_deriv z hz with ⟨Dψ, hψderiv, _⟩
    exact hψderiv.continuousAt.continuousWithinAt

  have hfibre_deriv_zero (z : Fin s → ℝ) (hz : z ∈ Metric.ball 0 ε) :
      HasFDerivAt (fun w ↦ f (ψ w))
        (0 : (Fin s → ℝ) →L[ℝ] F) z := by
    rcases hslice_deriv z hz with ⟨Dψ, hψderiv, hfcomp_zero⟩
    exact ((hf.differentiable_one (ψ z)).hasFDerivAt.comp z hψderiv).congr_fderiv
      hfcomp_zero

  have hfibre_const : ∀ z ∈ Metric.ball (0 : Fin s → ℝ) ε,
      f (ψ z) = f p := by
    intro z hz
    have hdiff : DifferentiableOn ℝ (fun w ↦ f (ψ w)) (Metric.ball 0 ε) :=
      fun w hw ↦ (hfibre_deriv_zero w hw).differentiableAt.differentiableWithinAt
    have hzero : ∀ w ∈ Metric.ball (0 : Fin s → ℝ) ε,
        fderivWithin ℝ (fun u ↦ f (ψ u)) (Metric.ball 0 ε) w = 0 := by
      intro w hw
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
      exact (hfibre_deriv_zero w hw).fderiv
    have heq := (convex_ball (0 : Fin s → ℝ) ε).is_const_of_fderivWithin_eq_zero
      hdiff hzero hz (Metric.mem_ball_self hε)
    simpa only [hψ0] using heq

  have hcover : A.ker ≤ Dψ0.range := by
    intro v hv
    have hvbar : v ∈ Abar.ker := by
      rw [← hker_base]
      exact hv
    let vker : Abar.ker := ⟨v, hvbar⟩
    let z : Fin s → ℝ := kernelCoordinates vker
    have hQv : Q v = vker := by
      simpa only [vker] using hQ vker
    have hDψv : Dψ0 z = v := by
      have hcharacterization :=
        Φ.fderiv_implicitFunction_apply_eq_iff (x := z) (y := v)
      have hconditions : Φ.leftDeriv v = 0 ∧ Φ.rightDeriv v = z := by
        constructor
        · exact hvbar
        · change Qcoord v = z
          change kernelCoordinates (Q v) = kernelCoordinates vker
          rw [hQv]
      have hresult := hcharacterization.mpr hconditions
      simpa only [Dψ0, ψ, chart, Φ, k, sub_self, map_zero,
        ImplicitFunctionData.implicitFunction_apply] using hresult
    exact ⟨z, hDψv⟩

  exact ⟨s, ψ, ε, hε, hψ0, hψderiv0.differentiableAt,
    hψ_continuous, hfibre_const, hcover⟩

/-- Let `p` be a maximum-rank point of a `C¹` map `f`.  If a second `C¹`
map `g` is locally constant on the fibre of `f` through `p`, then every
infinitesimal direction preserving `f` at `p` also preserves `g` there. -/
theorem ker_fderiv_le_of_eventually_level_imp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {f : E → F} {g : E → G} {p : E}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hmax : ∀ q,
      Module.finrank ℝ (fderiv ℝ f q).range ≤
        Module.finrank ℝ (fderiv ℝ f p).range)
    (hlevel : ∀ᶠ q in 𝓝 p, f q = f p → g q = g p) :
    (fderiv ℝ f p).ker ≤ (fderiv ℝ g p).ker := by
  rcases exists_regular_fibre_slice hf hmax with
    ⟨s, ψ, ε, hε, hψ0, hψdiff, _, hfibre, hcover⟩
  have hψtendsto : Tendsto ψ (𝓝 0) (𝓝 p) := by
    rw [← hψ0]
    exact hψdiff.continuousAt
  have hfibre_eventually : ∀ᶠ z in 𝓝 (0 : Fin s → ℝ), f (ψ z) = f p := by
    filter_upwards [Metric.ball_mem_nhds 0 hε] with z hz
    exact hfibre z hz
  have hlevel_along : ∀ᶠ z in 𝓝 (0 : Fin s → ℝ),
      f (ψ z) = f p → g (ψ z) = g p := hψtendsto hlevel
  have hg_along : (fun z ↦ g (ψ z)) =ᶠ[𝓝 (0 : Fin s → ℝ)]
      (fun _ ↦ g p) := by
    filter_upwards [hfibre_eventually, hlevel_along] with z hzf hzg
    exact hzg hzf
  have hg_at : HasFDerivAt g (fderiv ℝ g p) (ψ 0) := by
    simpa only [hψ0] using (hg.differentiable_one p).hasFDerivAt
  have hgcomp : HasFDerivAt (fun z ↦ g (ψ z))
      ((fderiv ℝ g p).comp (fderiv ℝ ψ 0)) 0 :=
    hg_at.comp 0 hψdiff.hasFDerivAt
  have hgcomp_zero : (fderiv ℝ g p).comp (fderiv ℝ ψ 0) = 0 :=
    hgcomp.unique (hasFDerivAt_zero_of_eventually_const (g p) hg_along)
  intro v hv
  rcases hcover hv with ⟨z, hz⟩
  have hz0 := DFunLike.congr_fun hgcomp_zero z
  change fderiv ℝ g p (fderiv ℝ ψ 0 z) = 0 at hz0
  change fderiv ℝ g p v = 0
  calc
    fderiv ℝ g p v = fderiv ℝ g p (fderiv ℝ ψ 0 z) :=
      congrArg (fderiv ℝ g p) hz.symm
    _ = 0 := hz0

end

end RB31E2E
