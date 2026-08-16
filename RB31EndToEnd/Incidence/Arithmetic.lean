import Mathlib

/-!
# Integer arithmetic for the sparse-skeleton and bad-pin estimates

These statements are deliberately separated from the geometric facts
that supply their hypotheses.
-/

namespace RB31E2E

structure TraceCounts where
  t : ℤ
  q : ℤ
  mInt : ℤ
  mCross : ℤ
  sInt : ℤ
  sCross : ℤ

def TraceCounts.Valid (d : TraceCounts) : Prop :=
  1 ≤ d.q ∧ d.q ≤ d.t ∧
  0 ≤ d.mInt ∧ 0 ≤ d.mCross ∧
  0 ≤ d.sInt ∧ 0 ≤ d.sCross ∧
  d.sInt ≤ d.mInt ∧
  6 * (d.t - 1) ≤
    2 * (d.mInt + d.mCross) + (d.sInt + d.sCross) ∧
  6 * (d.q - 1) ≤ 2 * d.mCross + d.sCross

def TraceCounts.requiredEdges (d : TraceCounts) : ℤ :=
  6 * (d.t - 1) - 2 * (d.mInt + d.mCross)

def TraceCounts.sparsePartitionTerm (d : TraceCounts) : ℤ :=
  2 * (d.t - d.q) + d.sCross

theorem partitionCondition_sparsePartitionTerm_ge
    (d : TraceCounts) (h : d.Valid) :
    d.requiredEdges ≤ d.sparsePartitionTerm := by
  rcases h with
    ⟨hqOne, hqt, hmInt, hmCross, hsInt, hsCross,
      hsIntMInt, hFine, hCoarse⟩
  simp only [TraceCounts.requiredEdges, TraceCounts.sparsePartitionTerm]
  omega

theorem strictOrbitDeficit
    (t M N R : ℤ) (hR : 6 * (t - 1) - 2 * M ≤ R) :
    6 * (t - 1) - R + M + 3 * (N - M) - 1 ≤ 3 * N - 1 := by
  omega

theorem badPin_dimension_arithmetic (t M N : ℤ) :
    let R := max 0 (6 * (t - 1) - 2 * M)
    6 * (t - 1) - R + M + 3 * (N - M) - 1 ≤ 3 * N - 1 := by
  dsimp
  apply strictOrbitDeficit
  exact Int.le_max_right _ _

/-- The exact sparse-null skeleton equation always pays the full grounded
twist-variable budget, including the branch where natural-number subtraction
has truncated to zero.  This is the arithmetic inequality used by the
relative-height chart argument. -/
theorem sparseNull_relativeHeight_budget
    (vertexCount activeCount edgeCount : ℕ)
    (hcard : edgeCount =
      6 * (vertexCount - 1) - 2 * activeCount) :
    6 * (vertexCount - 1) ≤ edgeCount + 2 * activeCount := by
  omega

end RB31E2E
