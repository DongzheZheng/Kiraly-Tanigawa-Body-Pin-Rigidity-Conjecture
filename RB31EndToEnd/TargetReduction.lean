import RB31EndToEnd.Rigidity.GraphNecessity
import RB31EndToEnd.Target

/-!
# Reduction of the body--pin equivalence to sufficiency

The necessity direction is already a theorem.  Consequently the body--pin
equivalence is equivalent to the partition-to-generic-rigidity implication.
This file proves that logical reduction without assuming sufficiency.
-/

namespace RB31E2E

/-- The body--pin equivalence is equivalent to its sufficiency direction once
necessity is known. -/
theorem endToEndBodyPinStatement_iff_sufficiency :
    EndToEndBodyPinStatement ↔
      ∀ (H : BodyPinIncidence) (extra : H.Body → ℕ),
        H.PartitionCondition → H.GenericallyRigidInR3 extra := by
  constructor
  · intro h H extra hPartition
    exact (h H extra).2 hPartition
  · intro h H extra
    constructor
    · exact H.partitionCondition_of_genericallyRigidInR3 extra
    · exact h H extra

end RB31E2E
