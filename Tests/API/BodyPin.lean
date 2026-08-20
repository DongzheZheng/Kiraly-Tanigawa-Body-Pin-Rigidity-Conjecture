import RB31EndToEnd.API.BodyPin

/-! A consumer of the public body--pin facade and no other project facade. -/

open scoped BigOperators

namespace PublicAPISmoke.BodyPin

def pinCapacity (m : ℕ) : ℕ :=
  RB31E2E.pinCapacity m

def makeBodyPinIncidence
    (Body Pin : Type)
    [Fintype Body] [Fintype Pin]
    [DecidableEq Body] [DecidableEq Pin]
    (left right : Pin → Body)
    (loopless : ∀ e, left e ≠ right e) :
    RB31E2E.BodyPinIncidence where
  Body := Body
  Pin := Pin
  bodyFinite := inferInstance
  pinFinite := inferInstance
  bodyDecidableEq := inferInstance
  pinDecidableEq := inferInstance
  left := left
  right := right
  loopless := loopless

example
    (Body Pin : Type)
    [Fintype Body] [Fintype Pin]
    [DecidableEq Body] [DecidableEq Pin]
    (left right : Pin → Body)
    (loopless : ∀ e, left e ≠ right e)
    (e : Pin) :
    (makeBodyPinIncidence Body Pin left right loopless).left e = left e :=
  rfl

def capacityOfPartition
    (H : RB31E2E.BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) : ℕ :=
  H.partitionCapacity label

def finpartitionCapacity
    (H : RB31E2E.BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) : ℕ :=
  H.finpartitionCapacity P

def partitionCondition (H : RB31E2E.BodyPinIncidence) : Prop :=
  H.PartitionCondition

def finpartitionCondition (H : RB31E2E.BodyPinIncidence) : Prop :=
  H.FinpartitionCondition

example (H : RB31E2E.BodyPinIncidence) :
    H.PartitionCondition ↔ H.FinpartitionCondition :=
  H.partitionCondition_iff_finpartitionCondition

def bodyPinGraph
    (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) :
    SimpleGraph (H.BPVertex extra) :=
  H.bodyPinGraph extra

def canonicalBodyPinGraph (H : RB31E2E.BodyPinIncidence) :
    SimpleGraph (H.BPVertex fun _ ↦ 0) :=
  H.canonicalBodyPinGraph

def genericallyRigidInR3
    (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) : Prop :=
  H.GenericallyRigidInR3 extra

example (m : ℕ) :
    RB31E2E.BarJoint.completeFrameworkRankTarget 3 m +
        RB31E2E.pinCapacity m =
      3 * m :=
  RB31E2E.completeFrameworkRankTarget_three_add_pinCapacity m

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

end PublicAPISmoke.BodyPin
