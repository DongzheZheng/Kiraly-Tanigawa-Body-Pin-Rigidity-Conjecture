import RB31EndToEnd.API.BarJoint

/-! A consumer of the public bar--joint facade and no other project facade. -/

namespace PublicAPISmoke.BarJoint

def expandedPoint (d : ℕ) : Type :=
  Fin d → ℝ

example (d : ℕ) :
    RB31E2E.BarJoint.Point d = expandedPoint d :=
  rfl

example (d : ℕ) :
    expandedPoint d = RB31E2E.BarJoint.Point d :=
  rfl

def expandedPlacement (V : Type) (d : ℕ) : Type :=
  V → Fin d → ℝ

example (V : Type) (d : ℕ) :
    RB31E2E.BarJoint.Placement V d = expandedPlacement V d :=
  rfl

example (V : Type) (d : ℕ) :
    expandedPlacement V d = RB31E2E.BarJoint.Placement V d :=
  rfl

def expandedVelocity (V : Type) (d : ℕ) : Type :=
  V → Fin d → ℝ

example (V : Type) (d : ℕ) :
    RB31E2E.BarJoint.Velocity V d = expandedVelocity V d :=
  rfl

example (V : Type) (d : ℕ) :
    expandedVelocity V d = RB31E2E.BarJoint.Velocity V d :=
  rfl

def edgeConstraint
    {V : Type} {d : ℕ}
    (p : RB31E2E.BarJoint.Placement V d)
    (u : RB31E2E.BarJoint.Velocity V d) (v w : V) : ℝ :=
  RB31E2E.BarJoint.edgeConstraint p u v w

def edgeFunctional
    {V : Type} {d : ℕ}
    (p : RB31E2E.BarJoint.Placement V d) (v w : V) :
    RB31E2E.BarJoint.Velocity V d →ₗ[ℝ] ℝ :=
  RB31E2E.BarJoint.edgeFunctional p v w

noncomputable def rigidityOperator
    {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p : RB31E2E.BarJoint.Placement V d) :
    RB31E2E.BarJoint.Velocity V d →ₗ[ℝ] (V × V → ℝ) :=
  RB31E2E.BarJoint.rigidityOperator G p

def isInfinitesimalMotion
    {V : Type} {d : ℕ} (G : SimpleGraph V)
    (p : RB31E2E.BarJoint.Placement V d)
    (u : RB31E2E.BarJoint.Velocity V d) : Prop :=
  RB31E2E.BarJoint.IsInfinitesimalMotion G p u

noncomputable def rigidityRank
    {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : RB31E2E.BarJoint.Placement V d) : ℕ :=
  RB31E2E.BarJoint.rigidityRank G p

def rankIsAttained
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (d r : ℕ) : Prop :=
  RB31E2E.BarJoint.RankIsAttained G d r

noncomputable def genericRigidityRank
    {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ) : ℕ :=
  RB31E2E.BarJoint.genericRigidityRank G d

example {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    ∃ p : RB31E2E.BarJoint.Placement V d,
      RB31E2E.BarJoint.rigidityRank G p =
        RB31E2E.BarJoint.genericRigidityRank G d :=
  RB31E2E.BarJoint.exists_rigidityRank_eq_genericRigidityRank G d

def isGenericallyRigidInDimension
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  RB31E2E.BarJoint.IsGenericallyRigidInDimension G d

def isGenericallyRigidInR3
    {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  RB31E2E.BarJoint.IsGenericallyRigidInR3 G

def completeFrameworkRankTarget (d n : ℕ) : ℕ :=
  RB31E2E.BarJoint.completeFrameworkRankTarget d n

end PublicAPISmoke.BarJoint
