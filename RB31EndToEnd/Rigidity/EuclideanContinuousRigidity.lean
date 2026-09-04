import RB31EndToEnd.Rigidity.ContinuousAsimowRoth

/-!
# Generic continuous rigidity in Euclidean coordinates

The coordinate-to-Euclidean homeomorphism transports both continuous motions
and open dense sets of placements. Thus the generic continuous-rigidity
criterion can be stated directly in native Euclidean space.
-/

namespace RB31E2E.BarJoint

variable {V : Type} [Fintype V]

/-- Continuous rigidity on an open dense set of native Euclidean placements. -/
def EuclideanIsGenericallyContinuouslyRigid (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ U : Set (V → EuclideanSpace ℝ (Fin d)), IsOpen U ∧ Dense U ∧
    ∀ p ∈ U, EuclideanIsContinuouslyRigid G p

/-- The two coordinate representations give the same generic
continuous-rigidity property. -/
theorem isGenericallyContinuouslyRigid_iff_euclidean
    (G : SimpleGraph V) (d : ℕ) :
    IsGenericallyContinuouslyRigid G d ↔ EuclideanIsGenericallyContinuouslyRigid G d := by
  let e := (placementEuclideanEquiv (V := V) (d := d)).toHomeomorph
  constructor
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    refine ⟨e '' U, e.isOpenMap U hUopen,
      e.surjective.denseRange.dense_image e.continuous hUdense, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    exact (isContinuouslyRigid_iff_euclideanIsContinuouslyRigid G p).mp (hUrigid p hp)
  · rintro ⟨U, hUopen, hUdense, hUrigid⟩
    refine ⟨e.symm '' U, e.symm.isOpenMap U hUopen,
      e.symm.surjective.denseRange.dense_image e.symm.continuous hUdense, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    apply (isContinuouslyRigid_iff_euclideanIsContinuouslyRigid G (e.symm p)).mpr
    change EuclideanIsContinuouslyRigid G (e (e.symm p))
    simpa only [e.apply_symm_apply] using hUrigid p hp

/-- Native Euclidean generic continuous rigidity is equivalent to maximum rank. -/
theorem euclideanIsGenericallyContinuouslyRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (d : ℕ) :
    EuclideanIsGenericallyContinuouslyRigid G d ↔ IsGenericallyRigidInDimension G d :=
  (isGenericallyContinuouslyRigid_iff_euclidean G d).symm.trans
    (isGenericallyContinuouslyRigid_iff_isGenericallyRigid G d)

/-- Generic continuous and local rigidity agree in native Euclidean space. -/
theorem euclideanIsGenericallyContinuouslyRigid_iff_locallyRigid
    (G : SimpleGraph V) (d : ℕ) :
    EuclideanIsGenericallyContinuouslyRigid G d ↔ EuclideanIsGenericallyLocallyRigid G d :=
  (euclideanIsGenericallyContinuouslyRigid_iff_isGenericallyRigid G d).trans
    (euclideanIsGenericallyLocallyRigid_iff_isGenericallyRigid G d).symm

end RB31E2E.BarJoint
