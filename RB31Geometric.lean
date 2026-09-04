import RB31EndToEnd
import RB31EndToEnd.Rigidity.AsimowRoth
import RB31EndToEnd.Rigidity.PathRigidity
import RB31EndToEnd.Rigidity.EuclideanContinuousRigidity

/-!
# The body--pin partition theorem in Euclidean geometric form

The geometric statements use preservation of actual Euclidean edge lengths
and congruence of labelled placements. Their proofs combine the closed
maximum-rank theorem with the proved local- and continuous-rigidity equivalences.
-/

namespace RB31E2E

/-- The partition criterion is equivalent to local Euclidean rigidity on an
open dense set of placements of the expanded body--pin graph. -/
def EndToEndGeometricBodyPinStatement : Prop :=
  ∀ (H : BodyPinIncidence) (extra : H.Body → ℕ),
    BarJoint.EuclideanIsGenericallyLocallyRigid (H.bodyPinGraph extra) 3 ↔ H.PartitionCondition

/-- The unconditional body--pin theorem in geometric local-rigidity form. -/
theorem endToEndGeometricBodyPinStatement : EndToEndGeometricBodyPinStatement := by
  intro H extra
  exact (BarJoint.euclideanIsGenericallyLocallyRigid_iff_isGenericallyRigid
    (H.bodyPinGraph extra) 3).trans (endToEndBodyPinStatement H extra)

/-- The partition criterion in the open-dense Euclidean continuous-rigidity
formulation, quantifying over all continuous motions. -/
def EndToEndContinuousBodyPinStatement : Prop :=
  ∀ (H : BodyPinIncidence) (extra : H.Body → ℕ),
    BarJoint.EuclideanIsGenericallyContinuouslyRigid (H.bodyPinGraph extra) 3 ↔
      H.PartitionCondition

/-- The unconditional body--pin theorem in continuous Euclidean rigidity form. -/
theorem endToEndContinuousBodyPinStatement : EndToEndContinuousBodyPinStatement := by
  intro H extra
  exact (BarJoint.euclideanIsGenericallyContinuouslyRigid_iff_isGenericallyRigid
    (H.bodyPinGraph extra) 3).trans (endToEndBodyPinStatement H extra)

/-- At every simultaneously regular real placement of the expanded graph,
ordinary local Euclidean rigidity is equivalent to the partition criterion. -/
theorem bodyPin_isLocallyRigid_iff_partition_of_isGenericPlacement
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hp : BarJoint.IsGenericPlacement p) :
    BarJoint.IsLocallyRigid (H.bodyPinGraph extra) p ↔ H.PartitionCondition :=
  (BarJoint.isLocallyRigid_iff_of_isGenericPlacement (H.bodyPinGraph extra) p hp).trans
    (endToEndBodyPinStatement H extra)

/-- Under the partition criterion, every continuous edge-length-preserving
motion from a regular placement remains congruent to that placement. -/
theorem bodyPin_isContinuouslyRigid_of_partition_of_regular
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hp : BarJoint.IsRegularPlacement (H.bodyPinGraph extra) p)
    (hpart : H.PartitionCondition) :
    BarJoint.IsContinuouslyRigid (H.bodyPinGraph extra) p := by
  have hr := (endToEndBodyPinStatement H extra).mpr hpart
  exact BarJoint.isContinuouslyRigid_of_rigidityRank_eq_complete_genericRank
    (H.bodyPinGraph extra) p (hp.trans hr)

/-- The continuous-motion conclusion in native Euclidean coordinates. -/
theorem bodyPin_euclideanIsContinuouslyRigid_of_partition_of_regular
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (p : BarJoint.Placement (H.BPVertex extra) 3)
    (hp : BarJoint.IsRegularPlacement (H.bodyPinGraph extra) p)
    (hpart : H.PartitionCondition) :
    BarJoint.EuclideanIsContinuouslyRigid (H.bodyPinGraph extra)
      (BarJoint.toEuclideanPlacement p) :=
  (BarJoint.isContinuouslyRigid_iff_euclideanIsContinuouslyRigid _ _).mp
    (bodyPin_isContinuouslyRigid_of_partition_of_regular H extra p hp hpart)

end RB31E2E
