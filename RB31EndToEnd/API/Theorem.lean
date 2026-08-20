import RB31EndToEnd

/-!
# Explicit end-to-end theorem facade

This deliberately heavy facade exposes the unconditional body--pin theorem.
Import `RB31EndToEnd.API` instead when the capstone is not required.
-/

namespace RB31E2E

/-- Direct consumer form of the three-dimensional body--pin partition theorem. -/
theorem BodyPinIncidence.genericallyRigidInR3_iff_partitionCondition
    (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition :=
  endToEndBodyPinStatement H extra

end RB31E2E
