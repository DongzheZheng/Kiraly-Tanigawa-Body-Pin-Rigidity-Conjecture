import RB31EndToEnd.NullCellule.ProvenanceFlagSemismallnessFinal
import RB31EndToEnd.NullCellule.ProvenanceFlagGroundedPF

/-!
# Three-dimensional body--pin rigidity

This root module states the unconditional end-to-end theorem proved by the
library.
-/

namespace RB31E2E

/-- The three-dimensional body--pin partition theorem in maximum-rank form. -/
theorem endToEndBodyPinStatement : EndToEndBodyPinStatement :=
  ProvenanceFlagGroundedPF.endToEndBodyPinStatement_of_provenanceFlag_semismallness
    ProvenanceFlag.provenanceFlag_semismallness

end RB31E2E
