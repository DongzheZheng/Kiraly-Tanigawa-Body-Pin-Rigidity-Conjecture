import RB31EndToEnd.Rigidity.BodyPinGraph

/-!
# Exact end-to-end target

This file records the proposition to be inhabited.  It does not assert
the conjecture and introduces no mathematical assumption.
-/

namespace RB31E2E

/--
For every finite loopless body--pin multigraph and every permitted
number of additional private body vertices, the literal partition
condition is equivalent to maximum-rank generic bar--joint rigidity of
the actual expanded graph in `ℝ³`.
-/
def EndToEndBodyPinStatement : Prop :=
  ∀ (H : BodyPinIncidence) (extra : H.Body → ℕ),
    H.GenericallyRigidInR3 extra ↔ H.PartitionCondition

end RB31E2E
