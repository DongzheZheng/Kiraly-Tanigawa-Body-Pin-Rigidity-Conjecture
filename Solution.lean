import RB31EndToEnd.NullCellule.ProvenanceFlagSemismallnessFinal
import RB31EndToEnd.NullCellule.ProvenanceFlagGroundedPF

/-!
# Three-dimensional body--pin rigidity: comparator solution

This module restates the challenge theorem and supplies the proof from the
production development.  It intentionally does not import `RB31EndToEnd`,
whose root module declares the same theorem name.
-/

namespace RB31E2E

/-- The proved solution corresponding to `Challenge.lean`. -/
theorem endToEndBodyPinStatement : EndToEndBodyPinStatement :=
  ProvenanceFlagGroundedPF.endToEndBodyPinStatement_of_provenanceFlag_semismallness
    ProvenanceFlag.provenanceFlag_semismallness

end RB31E2E
