import RB31EndToEnd.API.Theorem

/-! A consumer of the explicit heavy theorem facade and no other project facade. -/

namespace PublicAPISmoke.Theorem

example : RB31E2E.EndToEndBodyPinStatement :=
  RB31E2E.endToEndBodyPinStatement

example (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) :
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition :=
  RB31E2E.endToEndBodyPinStatement H extra

example (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) :
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition :=
  H.genericallyRigidInR3_iff_partitionCondition extra

end PublicAPISmoke.Theorem
