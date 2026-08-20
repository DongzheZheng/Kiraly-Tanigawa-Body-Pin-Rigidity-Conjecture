import RB31EndToEnd.API

/-!
# Default public API smoke test

This file exercises the supported default prelude without pulling in the
end-to-end theorem facade.  Each granular facade is tested independently in
`Tests/API/` so transitive imports cannot hide a missing facade dependency.
-/

open scoped BigOperators

namespace PublicAPISmoke.Prelude

example (m : ℕ) :
    RB31E2E.pinCapacity m +
        RB31E2E.BarJoint.completeFrameworkRankTarget 3 m =
      3 * m :=
  RB31E2E.pinCapacity_add_completeFrameworkRankTarget_three m

example {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) :
    (∑ i, RB31E2E.BarJoint.completeFrameworkRankTarget 3 (multiplicity i)) +
        (∑ i, RB31E2E.pinCapacity (multiplicity i)) =
      3 * ∑ i, multiplicity i :=
  RB31E2E.sum_completeFrameworkRankTarget_three_add_sum_pinCapacity multiplicity

end PublicAPISmoke.Prelude
