import RB31EndToEnd.Algebra.FiniteOpenIntersection
import RB31EndToEnd.Algebra.GroundedTwistPolynomial
import RB31EndToEnd.Incidence.EqualityPartition
import RB31EndToEnd.Rigidity.BodyTwistGenericBridge

/-!
# Finite assembly of fixed-partition bad-locus certificates

The geometric argument is indexed by the exact equality partition of a
non-diagonal twist assignment.  There are only finitely many such partitions.
This file proves the complete finite-union step in an explicitly algebraic
form: one nonzero integer polynomial vanishing on every bad realization of
each fixed partition yields a single real pin placement with no non-diagonal
motion, hence generic rigidity of the literal expanded body--pin graph.

No certificate is postulated globally.  The theorem below exposes the exact
per-partition certificate obligation that the null-cellule incidence bound
must construct.
-/

namespace RB31E2E

namespace BodyPinIncidence

noncomputable section

/-- The finite provenance type of exact equality partitions of body labels. -/
abbrev EqualityPartitionIndex (H : BodyPinIncidence) :=
  Finpartition (Finset.univ : Finset H.Body)

/-- A non-diagonal motion whose equality cellules are exactly `P`. -/
def ExactBadMotionAt (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) (p : H.Pin → Vec3 ℝ)
    (X : H.Body → Twist ℝ) : Prop :=
  IsTwistMotion H.left H.right p X ∧
    equalityPartition X = P ∧
      ¬ IsDiagonalTwist X

/-- Every bad motion belongs to the stratum indexed by its canonical exact
equality partition. -/
theorem exactBadMotionAt_equalityPartition
    (H : BodyPinIncidence) (p : H.Pin → Vec3 ℝ)
    (X : H.Body → Twist ℝ) (hMotion : IsTwistMotion H.left H.right p X)
    (hNonDiagonal : ¬ IsDiagonalTwist X) :
    H.ExactBadMotionAt (equalityPartition X) p X :=
  ⟨hMotion, rfl, hNonDiagonal⟩

/-- A finite family of nonzero polynomial certificates, one for each exact
equality partition, has a common real point outside every certified bad
locus.  At that point the actual twist system is rigid. -/
theorem exists_real_twistRigidAt_of_partitionCertificates
    (H : BodyPinIncidence)
    (certificate : H.EqualityPartitionIndex →
      MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ)
    (hNonzero : ∀ P, certificate P ≠ 0)
    (hVanish : ∀ (P : H.EqualityPartitionIndex)
        (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
      H.ExactBadMotionAt P p X →
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) (certificate P) = 0) :
    HasRigidTwistRealization (k := ℝ) H.left H.right := by
  classical
  let S : Finset
      (MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ) :=
    Finset.univ.image certificate
  have hSNonzero : ∀ Q ∈ S, Q ≠ 0 := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
    exact hNonzero P
  obtain ⟨z, hz⟩ :=
    ComplexRealSpecialization.exists_real_eval₂_ne_zero_all_int S hSNonzero
  let p : H.Pin → Vec3 ℝ :=
    GroundedTwistPolynomial.pinsOfAssignment z
  refine ⟨p, ?_⟩
  intro X hMotion
  by_contra hNonDiagonal
  let P : H.EqualityPartitionIndex := equalityPartition X
  have hBad : H.ExactBadMotionAt P p X :=
    H.exactBadMotionAt_equalityPartition p X hMotion hNonDiagonal
  have hCertificateMem : certificate P ∈ S := by
    exact Finset.mem_image.mpr ⟨P, Finset.mem_univ P, rfl⟩
  have hAvoid := hz (certificate P) hCertificateMem
  have hZero := hVanish P p X hBad
  apply hAvoid
  simpa [p] using hZero

/-- The same finite certificate packet reaches the actual generic expanded
bar--joint graph through the already verified twist/bar-motion bridge. -/
theorem genericallyRigidInR3_of_partitionCertificates
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (certificate : H.EqualityPartitionIndex →
      MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ)
    (hNonzero : ∀ P, certificate P ≠ 0)
    (hVanish : ∀ (P : H.EqualityPartitionIndex)
        (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
      H.ExactBadMotionAt P p X →
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) (certificate P) = 0) :
    H.GenericallyRigidInR3 extra := by
  apply H.genericallyRigidInR3_of_hasRigidTwistRealization extra
  exact H.exists_real_twistRigidAt_of_partitionCertificates
    certificate hNonzero hVanish

end

end BodyPinIncidence

end RB31E2E
