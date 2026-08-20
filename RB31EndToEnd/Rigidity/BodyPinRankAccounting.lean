import RB31EndToEnd.Combinatorics.BodyPinCapacity
import RB31EndToEnd.Rigidity.BarJoint

/-!
# Body--pin rank accounting

Reusable numerical bridges between the three-dimensional complete-framework
rank target and the capped contribution of a body--pin bundle.
-/

open scoped BigOperators

namespace RB31E2E

/-- In dimension three, the complete-framework rank target and body--pin
capacity split the three scalar coordinates supplied by `m` pin occurrences. -/
theorem completeFrameworkRankTarget_three_add_pinCapacity (m : ℕ) :
    BarJoint.completeFrameworkRankTarget 3 m + pinCapacity m = 3 * m := by
  by_cases hm : m ≤ 4
  · interval_cases m <;> decide
  · rw [pinCapacity_of_three_le (by omega)]
    simp only [BarJoint.completeFrameworkRankTarget, if_neg (by omega)]
    rw [show Nat.choose 4 2 = 6 by decide]
    omega

/-- Commuted form of `completeFrameworkRankTarget_three_add_pinCapacity`. -/
theorem pinCapacity_add_completeFrameworkRankTarget_three (m : ℕ) :
    pinCapacity m + BarJoint.completeFrameworkRankTarget 3 m = 3 * m := by
  calc
    pinCapacity m + BarJoint.completeFrameworkRankTarget 3 m =
        BarJoint.completeFrameworkRankTarget 3 m + pinCapacity m := Nat.add_comm _ _
    _ = 3 * m := completeFrameworkRankTarget_three_add_pinCapacity m

/-- Finite-family form of
`completeFrameworkRankTarget_three_add_pinCapacity`. -/
theorem sum_completeFrameworkRankTarget_three_add_sum_pinCapacity
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) :
    (∑ i, BarJoint.completeFrameworkRankTarget 3 (multiplicity i)) +
        (∑ i, pinCapacity (multiplicity i)) =
      3 * ∑ i, multiplicity i := by
  change
    (Finset.univ.sum fun i => BarJoint.completeFrameworkRankTarget 3 (multiplicity i)) +
        (Finset.univ.sum fun i => pinCapacity (multiplicity i)) =
      3 * Finset.univ.sum multiplicity
  rw [← Finset.sum_add_distrib]
  calc
    Finset.univ.sum
          (fun i => BarJoint.completeFrameworkRankTarget 3 (multiplicity i) +
            pinCapacity (multiplicity i)) =
        Finset.univ.sum (fun i => 3 * multiplicity i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact completeFrameworkRankTarget_three_add_pinCapacity (multiplicity i)
    _ = 3 * Finset.univ.sum multiplicity := by
      rw [Finset.mul_sum]

end RB31E2E
