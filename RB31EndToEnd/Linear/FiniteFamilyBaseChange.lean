import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Rank of a finite vector family under field extension

The rank of a finite labelled family of vectors does not change after
applying an injective field extension coordinatewise.  This is the exact
base-change fact needed when the child configuration of the flag induction
lives in its own coordinate function field.
-/

namespace RB31E2E

namespace FiniteFamilyBaseChange

noncomputable section

open Set Submodule

variable {L K I J : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [Finite J]

/-- Coordinatewise extension of scalars for a vector in a finite function
space. -/
def mapVector (x : J → L) : J → K :=
  algebraMap L K ∘ x

omit [Fintype I] in
/-- The span rank of a finite vector family is invariant under a field
extension. -/
theorem finrank_span_range_mapVector (v : I → J → L) :
    Module.finrank L (span L (Set.range v)) =
      Module.finrank K (span K (Set.range (fun i ↦ mapVector (K := K) (v i)))) := by
  letI : FaithfulSMul L K :=
    (faithfulSMul_iff_algebraMap_injective L K).2 (RingHom.injective _)
  let vK : I → J → K := fun i ↦ mapVector (K := K) (v i)
  apply Nat.le_antisymm
  · obtain ⟨f, hfmem, hfspan, hfLI⟩ :=
      exists_fun_fin_finrank_span_eq L (Set.range v)
    let fK : Fin (Module.finrank L (span L (Set.range v))) → J → K :=
      fun i ↦ mapVector (K := K) (f i)
    have hfKLI : LinearIndependent K fK := by
      exact (linearIndependent_algebraMap_comp_iff).2 hfLI
    have hfKsub : span K (Set.range fK) ≤ span K (Set.range vK) := by
      apply span_mono
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hfmem i
      refine ⟨j, ?_⟩
      dsimp [fK, vK, mapVector]
      exact congrArg (fun z : J → L ↦ algebraMap L K ∘ z) hj
    calc
      Module.finrank L (span L (Set.range v)) =
          Fintype.card (Fin (Module.finrank L (span L (Set.range v)))) := by
        simp
      _ = Module.finrank K (span K (Set.range fK)) := by
        symm
        exact finrank_span_eq_card hfKLI
      _ ≤ Module.finrank K (span K (Set.range vK)) :=
        Submodule.finrank_mono hfKsub
  · obtain ⟨g, hgmem, hgspan, hgLI⟩ :=
      exists_fun_fin_finrank_span_eq K (Set.range vK)
    choose idx hidx using hgmem
    have hgEq : g = fun i ↦ vK (idx i) := by
      funext i
      exact (hidx i).symm
    have hidxKLI : LinearIndependent K (fun i ↦ vK (idx i)) := by
      rw [← hgEq]
      exact hgLI
    have hidxLLI : LinearIndependent L (fun i ↦ v (idx i)) := by
      apply (linearIndependent_algebraMap_comp_iff
        (R := L) (S := K) (v := fun i ↦ v (idx i))).1
      simpa [vK, mapVector] using hidxKLI
    have hsub : span L (Set.range (fun i ↦ v (idx i))) ≤
        span L (Set.range v) := by
      apply span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨idx i, rfl⟩
    calc
      Module.finrank K (span K (Set.range vK)) =
          Fintype.card (Fin (Module.finrank K (span K (Set.range vK)))) := by
        simp
      _ = Module.finrank L
          (span L (Set.range (fun i ↦ v (idx i)))) := by
        symm
        exact finrank_span_eq_card hidxLLI
      _ ≤ Module.finrank L (span L (Set.range v)) :=
        Submodule.finrank_mono hsub

/-- The same rank-invariance statement for a family indexed by an arbitrary
finite type.  This is the form consumed by direction-row families. -/
theorem finrank_span_range_mapVector_finite
    {I' : Type*} [Finite I'] (v : I' → J → L) :
    Module.finrank L (span L (Set.range v)) =
      Module.finrank K
        (span K (Set.range (fun i ↦ mapVector (K := K) (v i)))) := by
  letI : Fintype I' := Fintype.ofFinite I'
  exact finrank_span_range_mapVector v

end

end FiniteFamilyBaseChange

end RB31E2E
