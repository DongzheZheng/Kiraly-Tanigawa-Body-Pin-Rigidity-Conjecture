import RB31Geometric

/- The expanded conclusion below uses only Euclidean distances, neighbourhoods,
open sets, density, and the original partition condition. -/
example (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) :
    (∃ U : Set (H.BPVertex extra → EuclideanSpace ℝ (Fin 3)),
      IsOpen U ∧ Dense U ∧ ∀ p ∈ U,
        ∀ᶠ q in nhds p,
          (∀ v w, (H.bodyPinGraph extra).Adj v w →
            dist (p v) (p w) = dist (q v) (q w)) →
          (∀ v w, dist (p v) (p w) = dist (q v) (q w))) ↔
      H.PartitionCondition :=
  RB31E2E.endToEndGeometricBodyPinStatement H extra

/- Continuous rigidity quantifies over every continuous motion, with no
differentiability condition, and asserts congruence at every time. -/
example (H : RB31E2E.BodyPinIncidence) (extra : H.Body → ℕ) :
    (∃ U : Set (H.BPVertex extra → EuclideanSpace ℝ (Fin 3)),
      IsOpen U ∧ Dense U ∧ ∀ p ∈ U,
        ∀ c : unitInterval → (H.BPVertex extra → EuclideanSpace ℝ (Fin 3)),
          Continuous c → c 0 = p →
          (∀ t v w, (H.bodyPinGraph extra).Adj v w →
            dist (p v) (p w) = dist (c t v) (c t w)) →
          (∀ t v w, dist (p v) (p w) = dist (c t v) (c t w))) ↔
      H.PartitionCondition :=
  RB31E2E.endToEndContinuousBodyPinStatement H extra

/- Small frameworks are included without a lower bound on the vertex count. -/
example (d : ℕ) :
    RB31E2E.BarJoint.EuclideanIsGenericallyLocallyRigid (⊤ : SimpleGraph (Fin 0)) d := by
  rw [RB31E2E.BarJoint.euclideanIsGenericallyLocallyRigid_iff_isGenericallyRigid]
  rfl

example (d : ℕ) :
    RB31E2E.BarJoint.EuclideanIsGenericallyLocallyRigid (⊤ : SimpleGraph (Fin 1)) d := by
  rw [RB31E2E.BarJoint.euclideanIsGenericallyLocallyRigid_iff_isGenericallyRigid]
  rfl

/- In zero-dimensional Euclidean space all placements are congruent. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    RB31E2E.BarJoint.EuclideanIsGenericallyLocallyRigid G 0 := by
  refine ⟨Set.univ, isOpen_univ, dense_univ, ?_⟩
  intro p _
  filter_upwards with q
  intro _ v w
  have hp : p v = p w := Subsingleton.elim _ _
  have hq : q v = q w := Subsingleton.elim _ _
  simp only [hp, hq, dist_self]
