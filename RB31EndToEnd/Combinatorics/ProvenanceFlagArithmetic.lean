import Mathlib.Tactic

/-!
# Arithmetic ledger for provenance flags

The graph-theoretic flag proof eventually reduces its two counting steps to
the elementary natural-number inequalities recorded here.  Keeping these
lemmas separate prevents later formalization from hiding a truncated
subtraction or an off-by-one error inside graph notation.
-/

namespace RB31E2E

namespace ProvenanceFlag

/-- A sparse union of `j` completed flag `K₄`s using `q` live terminals
must use at least `2*j+1` terminals.  The premise is written without
truncated subtraction. -/
theorem terminal_count_ge_two_mul_add_one
    {j q : ℕ} (_hj : 1 ≤ j) (hsparse : 6 * j + 2 ≤ 2 * (q + j)) :
    2 * j + 1 ≤ q := by
  omega

/-- The numerical contradiction underlying the low-degree selection lemma.

`o,p,s` count live vertices contained in zero, one, or at least two flags;
`h` is the total flag incidence contributed by the last class.  If every
zero-flag vertex had degree at least four and every private terminal had
degree at least three, the sparse completion edge budget would contradict
the incidence ledger. -/
theorem not_all_flag_degrees_large
    {n m k o p s h : ℕ}
    (hvertices : n = o + p + s)
    (hedges : m + 2 * k + 2 ≤ 2 * n)
    (hdegree : 4 * o + 3 * p + h ≤ 2 * m)
    (hincidence : p + h = 3 * k)
    (hmultiple : 2 * s ≤ h) : False := by
  omega

/-- Contrapositive packaging of the same ledger: under the sparse and flag
incidence budgets, the asserted global degree lower bound cannot hold. -/
theorem flag_selection_arithmetic
    {n m k o p s h : ℕ}
    (hvertices : n = o + p + s)
    (hedges : m + 2 * k + 2 ≤ 2 * n)
    (hincidence : p + h = 3 * k)
    (hmultiple : 2 * s ≤ h) :
    ¬ (4 * o + 3 * p + h ≤ 2 * m) := by
  intro hdegree
  exact not_all_flag_degrees_large hvertices hedges hdegree hincidence hmultiple

end ProvenanceFlag

end RB31E2E
