import RB31EndToEnd.API.BodyPin

/-!
# Dress-style downstream consumer smoke test

The consumer keeps its established names as thin wrappers around the provider
API and obtains the arithmetic identity without reopening the piecewise proof.
-/

namespace DressRigidityFormal

/-- Compatibility wrapper for the established Dress consumer name. -/
def bodyPinEll (m : ℕ) : ℕ :=
  RB31E2E.pinCapacity m

/-- Compatibility wrapper for the complete-separator rank target in dimension three. -/
def completeSeparatorRank (m : ℕ) : ℕ :=
  RB31E2E.BarJoint.completeFrameworkRankTarget 3 m

theorem completeSeparatorRank_add_bodyPinEll (m : ℕ) :
    completeSeparatorRank m + bodyPinEll m = 3 * m := by
  simpa [completeSeparatorRank, bodyPinEll] using
    RB31E2E.completeFrameworkRankTarget_three_add_pinCapacity m

end DressRigidityFormal
