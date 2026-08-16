import RB31EndToEnd.Specification

/-!
# Body--pin bundle capacity

Elementary facts about the `0,3,5,6` capacity table and the agreement
between occurrence-level unordered bundles and their oriented form.
-/

namespace RB31E2E

@[simp] theorem pinCapacity_zero : pinCapacity 0 = 0 := rfl
@[simp] theorem pinCapacity_one : pinCapacity 1 = 3 := rfl
@[simp] theorem pinCapacity_two : pinCapacity 2 = 5 := rfl

theorem pinCapacity_of_three_le {m : ℕ} (hm : 3 ≤ m) : pinCapacity m = 6 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity] at hm ⊢

theorem pinCapacity_le_six (m : ℕ) : pinCapacity m ≤ 6 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]

theorem pinCapacity_le_two_mul_add_one (m : ℕ) :
    pinCapacity m ≤ 2 * m + 1 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]
  all_goals omega

theorem pinCapacity_le_three_mul (m : ℕ) : pinCapacity m ≤ 3 * m := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]
  all_goals omega

theorem pinCapacity_eq_two_mul_add_one_of_one_or_two
    {m : ℕ} (hm : m = 1 ∨ m = 2) :
    pinCapacity m = 2 * m + 1 := by
  rcases hm with rfl | rfl <;> decide

/--
If `s` nonempty fine block-pairs carry `M` pins and every such pair
carries one or two pins, then aggregation into one capped bundle cannot
exceed the unaggregated `2M+s` budget.
-/
theorem pinCapacity_le_unaggregated (M s : ℕ)
    (hLower : s ≤ M) (hUpper : M ≤ 2 * s) :
    pinCapacity M ≤ 2 * M + s := by
  rcases M with _ | _ | _ | M <;> simp [pinCapacity]
  all_goals omega

theorem BodyPinIncidence.unorderedBundleMultiplicity_mk
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.unorderedBundleMultiplicity π s(i, j) = H.bundleMultiplicity π i j := by
  unfold unorderedBundleMultiplicity bundleMultiplicity
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff]

end RB31E2E
