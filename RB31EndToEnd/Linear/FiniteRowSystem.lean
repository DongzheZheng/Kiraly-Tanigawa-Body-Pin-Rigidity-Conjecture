import RB31EndToEnd.Linear.FiniteFamilyBaseChange
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite row systems and their stress ledger

This file packages a finite family of row vectors as both a constraint map
and its transpose synthesis map.  It proves the exact rank--nullity ledger
and invariance of the solution-space dimension under field extension.
-/

namespace RB31E2E

namespace FiniteRowSystem

noncomputable section

variable {k L I J : Type*}
  [Field k] [Fintype I] [Fintype J]

/-- Matrix of a labelled finite row family. -/
def matrix (row : J → I → k) : Matrix J I k := row

/-- Evaluation of the row family on a coordinate vector. -/
def constraint (row : J → I → k) : (I → k) →ₗ[k] (J → k) :=
  (matrix row).mulVecLin

/-- Transpose synthesis of labelled row weights. -/
def synthesis (row : J → I → k) : (J → k) →ₗ[k] (I → k) :=
  (matrix row).transpose.mulVecLin

/-- Dimension of the row-relation/stress space. -/
def stressDim (row : J → I → k) : ℕ :=
  Module.finrank k (LinearMap.ker (synthesis row))

theorem finrank_range_constraint_eq_finrank_range_synthesis
    (row : J → I → k) :
    Module.finrank k (LinearMap.range (constraint row)) =
      Module.finrank k (LinearMap.range (synthesis row)) := by
  change (matrix row).rank = (matrix row).transpose.rank
  exact (Matrix.rank_transpose (matrix row)).symm

/-- Subtraction-free row/solution/stress dimension identity. -/
theorem solutionDim_add_rowCard_eq_coordinateCard_add_stressDim
    (row : J → I → k) :
    Module.finrank k (LinearMap.ker (constraint row)) + Fintype.card J =
      Fintype.card I + stressDim row := by
  have hc := (constraint row).finrank_range_add_finrank_ker
  have hs := (synthesis row).finrank_range_add_finrank_ker
  have hcrange := finrank_range_constraint_eq_finrank_range_synthesis row
  have hI : Module.finrank k (I → k) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hJ : Module.finrank k (J → k) = Fintype.card J := by
    rw [Module.finrank_fintype_fun_eq_card]
  rw [hI] at hc
  rw [hJ] at hs
  dsimp [stressDim]
  omega

variable [Field L] [Algebra k L]

/-- Coordinatewise scalar extension of a row family. -/
def mapRows (row : J → I → k) : J → I → L :=
  fun j ↦ FiniteFamilyBaseChange.mapVector (K := L) (row j)

omit [Fintype J] in
theorem constraint_mapRows_mapVector
    (row : J → I → k) (x : I → k) :
    constraint (mapRows (L := L) row)
        (FiniteFamilyBaseChange.mapVector (K := L) x) =
      FiniteFamilyBaseChange.mapVector (K := L) (constraint row x) := by
  funext j
  simp only [constraint, matrix, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, mapRows, FiniteFamilyBaseChange.mapVector,
    Function.comp_apply, map_sum, map_mul]

/-- The constraint kernel dimension is invariant under field extension. -/
theorem finrank_ker_constraint_mapRows
    (row : J → I → k) :
    Module.finrank L (LinearMap.ker (constraint (mapRows (L := L) row))) =
      Module.finrank k (LinearMap.ker (constraint row)) := by
  have hrank :
      Module.finrank L
          (Submodule.span L (Set.range (mapRows (L := L) row))) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    exact (FiniteFamilyBaseChange.finrank_span_range_mapVector row).symm
  have hL := (constraint (mapRows (L := L) row)).finrank_range_add_finrank_ker
  have hk := (constraint row).finrank_range_add_finrank_ker
  have hrangeL :
      Module.finrank L
          (LinearMap.range (constraint (mapRows (L := L) row))) =
        Module.finrank L
          (Submodule.span L (Set.range (mapRows (L := L) row))) := by
    change (matrix (mapRows (L := L) row)).rank = _
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hrangek :
      Module.finrank k (LinearMap.range (constraint row)) =
        Module.finrank k (Submodule.span k (Set.range row)) := by
    change (matrix row).rank = _
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hI_L : Module.finrank L (I → L) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hI_k : Module.finrank k (I → k) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
  rw [hrangeL, hI_L] at hL
  rw [hrangek, hI_k] at hk
  omega

end

end FiniteRowSystem

end RB31E2E
