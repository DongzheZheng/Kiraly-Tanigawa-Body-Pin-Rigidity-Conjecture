import RB31EndToEnd.Incidence.CollinearityPolynomial
import RB31EndToEnd.Incidence.FiniteBadCover

/-!
# Provenance certificate for a triple pin bundle

Fix an exact equality partition of a body-twist assignment.  If three
distinct pin occurrences join the same two distinct equality blocks, the
same nonzero relative twist vanishes at all three pins.  Hence those three
pin positions are collinear and the explicit integer `2 × 2` minor from
`CollinearityPolynomial` vanishes.

The occurrence labels are retained throughout.  In particular, distinctness
of the three occurrences proves that the displayed polynomial is genuinely
nonzero; no genericity assertion is hidden in the certificate data.
-/

namespace RB31E2E

namespace BodyPinIncidence

noncomputable section

/-- An occurrence joins the unordered pair of blocks `A`, `B`.  Both endpoint
orientations are retained explicitly. -/
def PinJoinsBlocks (H : BodyPinIncidence) (P : H.EqualityPartitionIndex)
    (A B : P.parts) (e : H.Pin) : Prop :=
  (finpartitionBlock P (H.left e) = A ∧
      finpartitionBlock P (H.right e) = B) ∨
    (finpartitionBlock P (H.left e) = B ∧
      finpartitionBlock P (H.right e) = A)

/-- The explicit provenance-labelled polynomial attached to three pin
occurrences. -/
def tripleBundlePolynomial (H : BodyPinIncidence)
    (e₀ e₁ e₂ : H.Pin) :
    MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ :=
  PinCollinearity.minor01 e₀ e₁ e₂

/-- Three pairwise distinct occurrence labels make the triple-bundle
polynomial nonzero. -/
theorem tripleBundlePolynomial_ne_zero (H : BodyPinIncidence)
    {e₀ e₁ e₂ : H.Pin} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂)
    (h₁₂ : e₁ ≠ e₂) :
    H.tripleBundlePolynomial e₀ e₁ e₂ ≠ 0 := by
  exact PinCollinearity.minor01_ne_zero h₀₁ h₀₂ h₁₂

/-- Pin compatibility gives a zero of the canonically oriented relative
twist between the two exact equality blocks, regardless of the stored edge
orientation. -/
private theorem eval_equalityBlockValue_sub_eq_zero
    (H : BodyPinIncidence) (p : H.Pin → Vec3 ℝ)
    (X : H.Body → Twist ℝ)
    (A B : (equalityPartition X).parts) (e : H.Pin)
    (hJoin : H.PinJoinsBlocks (equalityPartition X) A B e)
    (hMotion : IsTwistMotion H.left H.right p X) :
    Twist.eval (equalityBlockValue X A - equalityBlockValue X B) (p e) = 0 := by
  rw [Twist.eval_sub]
  apply sub_eq_zero.mpr
  rcases hJoin with hForward | hReverse
  · have hLeft : X (H.left e) = equalityBlockValue X A := by
      rw [← equalityBlockValue_finpartitionBlock X (H.left e), hForward.1]
    have hRight : X (H.right e) = equalityBlockValue X B := by
      rw [← equalityBlockValue_finpartitionBlock X (H.right e), hForward.2]
    simpa only [hLeft, hRight] using hMotion e
  · have hLeft : X (H.left e) = equalityBlockValue X B := by
      rw [← equalityBlockValue_finpartitionBlock X (H.left e), hReverse.1]
    have hRight : X (H.right e) = equalityBlockValue X A := by
      rw [← equalityBlockValue_finpartitionBlock X (H.right e), hReverse.2]
    simpa only [hLeft, hRight] using (hMotion e).symm

/-- For one fixed exact partition and one specified triple bundle, the
explicit minor vanishes on every bad motion in that exact stratum. -/
theorem tripleBundlePolynomial_eq_zero_of_exactBadMotionAt
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex)
    (A B : P.parts) (hAB : A ≠ B) (e₀ e₁ e₂ : H.Pin)
    (hJoin₀ : H.PinJoinsBlocks P A B e₀)
    (hJoin₁ : H.PinJoinsBlocks P A B e₁)
    (hJoin₂ : H.PinJoinsBlocks P A B e₂)
    (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ)
    (hBad : H.ExactBadMotionAt P p X) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (GroundedTwistPolynomial.assignmentOfPins p)
        (H.tripleBundlePolynomial e₀ e₁ e₂) = 0 := by
  rcases hBad with ⟨hMotion, hPartition, _⟩
  subst P
  let Y : Twist ℝ := equalityBlockValue X A - equalityBlockValue X B
  have hY : Y ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hValues
    exact hAB (equalityBlockValue_injective X hValues)
  have hEval₀ : Twist.eval Y (p e₀) = 0 := by
    exact H.eval_equalityBlockValue_sub_eq_zero p X A B e₀ hJoin₀ hMotion
  have hEval₁ : Twist.eval Y (p e₁) = 0 := by
    exact H.eval_equalityBlockValue_sub_eq_zero p X A B e₁ hJoin₁ hMotion
  have hEval₂ : Twist.eval Y (p e₂) = 0 := by
    exact H.eval_equalityBlockValue_sub_eq_zero p X A B e₂ hJoin₂ hMotion
  exact PinCollinearity.minor01_eq_zero_of_common_twist
    p e₀ e₁ e₂ Y hY hEval₀ hEval₁ hEval₂

/-- A complete fixed-partition certificate packet for one triple pin bundle.
Its fields contain only combinatorial provenance; nonvanishing and bad-locus
vanishing are derived theorems below. -/
structure TripleBundlePartitionCertificate
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex) where
  first : H.Pin
  second : H.Pin
  third : H.Pin
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  blockA : P.parts
  blockB : P.parts
  blocks_ne : blockA ≠ blockB
  first_joins : H.PinJoinsBlocks P blockA blockB first
  second_joins : H.PinJoinsBlocks P blockA blockB second
  third_joins : H.PinJoinsBlocks P blockA blockB third

namespace TripleBundlePartitionCertificate

/-- The certificate in exactly the polynomial type consumed by
`exists_real_twistRigidAt_of_partitionCertificates`. -/
def polynomial {H : BodyPinIncidence} {P : H.EqualityPartitionIndex}
    (C : H.TripleBundlePartitionCertificate P) :
    MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ :=
  H.tripleBundlePolynomial C.first C.second C.third

theorem polynomial_ne_zero {H : BodyPinIncidence}
    {P : H.EqualityPartitionIndex}
    (C : H.TripleBundlePartitionCertificate P) : C.polynomial ≠ 0 := by
  exact H.tripleBundlePolynomial_ne_zero
    C.first_ne_second C.first_ne_third C.second_ne_third

theorem polynomial_eq_zero_of_exactBadMotionAt
    {H : BodyPinIncidence} {P : H.EqualityPartitionIndex}
    (C : H.TripleBundlePartitionCertificate P)
    (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ)
    (hBad : H.ExactBadMotionAt P p X) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (GroundedTwistPolynomial.assignmentOfPins p) C.polynomial = 0 := by
  exact H.tripleBundlePolynomial_eq_zero_of_exactBadMotionAt
    P C.blockA C.blockB C.blocks_ne C.first C.second C.third
    C.first_joins C.second_joins C.third_joins p X hBad

end TripleBundlePartitionCertificate

/-- If every exact equality stratum which actually contains a bad motion has
a certified triple bundle, the finite bad-locus theorem produces an actual
rigid real twist realization.  Empty strata receive the constant certificate
`1`; thus the hypothesis is not vacuous at the one-block partition. -/
theorem exists_real_twistRigidAt_of_tripleBundleCertificates_on_badStrata
    (H : BodyPinIncidence)
    (C : ∀ (P : H.EqualityPartitionIndex),
      (∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
        H.ExactBadMotionAt P p X) →
      H.TripleBundlePartitionCertificate P) :
    HasRigidTwistRealization (k := ℝ) H.left H.right := by
  classical
  let certificate : H.EqualityPartitionIndex →
      MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ :=
    fun P ↦ if hP : ∃ (p : H.Pin → Vec3 ℝ)
        (X : H.Body → Twist ℝ), H.ExactBadMotionAt P p X then
      (C P hP).polynomial else 1
  apply H.exists_real_twistRigidAt_of_partitionCertificates
    certificate
  · intro P
    dsimp only [certificate]
    split
    · next hP => exact (C P hP).polynomial_ne_zero
    · simp
  · intro P p X hBad
    dsimp only [certificate]
    rw [dif_pos ⟨p, X, hBad⟩]
    exact (C P ⟨p, X, hBad⟩).polynomial_eq_zero_of_exactBadMotionAt
      p X hBad

/-- The same packet reaches the literal expanded bar--joint generic-rigidity
semantics through the verified body-twist bridge. -/
theorem genericallyRigidInR3_of_tripleBundleCertificates_on_badStrata
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (C : ∀ (P : H.EqualityPartitionIndex),
      (∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
        H.ExactBadMotionAt P p X) →
      H.TripleBundlePartitionCertificate P) :
    H.GenericallyRigidInR3 extra := by
  apply H.genericallyRigidInR3_of_hasRigidTwistRealization extra
  exact H.exists_real_twistRigidAt_of_tripleBundleCertificates_on_badStrata C

end

end BodyPinIncidence

end RB31E2E
