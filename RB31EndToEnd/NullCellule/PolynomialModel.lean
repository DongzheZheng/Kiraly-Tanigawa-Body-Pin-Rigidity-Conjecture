import RB31EndToEnd.NullCellule.Definitions

/-!
# Polynomial model of Split--Klein null cellules

The six coordinates at every vertex are retained as provenance-labelled
variables.  Evaluating the universal twist at a concrete twist assignment is
definitionally the original assignment, and each unordered edge polynomial
evaluates to the corresponding Split--Klein null-difference equation.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- Six provenance-labelled coordinates at each vertex.  `false` denotes an
angular coordinate and `true` a translational coordinate. -/
abbrev TwistVariable (V : Type*) := V × (Bool × Fin 3)

/-- The universal angular coordinate at vertex `v`. -/
def angularCoordinate {k V : Type*} [CommRing k] (v : V) (i : Fin 3) :
    MvPolynomial (TwistVariable V) k :=
  X ⟨v, false, i⟩

/-- The universal translational coordinate at vertex `v`. -/
def translationalCoordinate {k V : Type*} [CommRing k] (v : V) (i : Fin 3) :
    MvPolynomial (TwistVariable V) k :=
  X ⟨v, true, i⟩

/-- The universal six-coordinate twist attached to a vertex. -/
def universalTwist {k V : Type*} [CommRing k] (v : V) :
    Twist (MvPolynomial (TwistVariable V) k) :=
  ⟨angularCoordinate v, translationalCoordinate v⟩

/-- Turn a concrete vertex-labelled twist configuration into an assignment of
all provenance-labelled polynomial variables. -/
def assignmentOfTwists {k V : Type*} [CommRing k]
    (Y : V → Twist k) : TwistVariable V → k
  | ⟨v, false, i⟩ => (Y v).1 i
  | ⟨v, true, i⟩ => (Y v).2 i

/-- Evaluate the six coordinate polynomials of a polynomial-valued twist. -/
def evalPolynomialTwist {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (T : Twist (MvPolynomial (TwistVariable V) k)) : Twist k :=
  ⟨fun i ↦ eval a (T.1 i), fun i ↦ eval a (T.2 i)⟩

@[simp]
theorem evalPolynomialTwist_universal {k V : Type*} [CommRing k]
    (Y : V → Twist k) (v : V) :
    evalPolynomialTwist (assignmentOfTwists Y) (universalTwist v) = Y v := by
  apply Prod.ext
  · funext i
    simp [evalPolynomialTwist, universalTwist, angularCoordinate,
      assignmentOfTwists]
  · funext i
    simp [evalPolynomialTwist, universalTwist, translationalCoordinate,
      assignmentOfTwists]

@[simp]
theorem evalPolynomialTwist_sub {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (S T : Twist (MvPolynomial (TwistVariable V) k)) :
    evalPolynomialTwist a (S - T) =
      evalPolynomialTwist a S - evalPolynomialTwist a T := by
  apply Prod.ext <;> funext i <;> simp [evalPolynomialTwist]

/-- Evaluation commutes with the Split--Klein quadratic form. -/
theorem eval_splitKlein {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (T : Twist (MvPolynomial (TwistVariable V) k)) :
    eval a (Twist.splitKlein T) =
      Twist.splitKlein (evalPolynomialTwist a T) := by
  simp [Twist.splitKlein, Vec3.dot, evalPolynomialTwist]

/-- The orientation-independent scalar null-difference value of an edge. -/
def nullDifferenceValue {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) : k :=
  Sym2.lift ⟨fun u v ↦ Twist.splitKlein (Y u - Y v), by
    intro u v
    exact Twist.splitKlein_sub_comm _ _⟩ e.1

/-- The orientation-independent Split--Klein quadratic attached to an edge. -/
def edgePolynomial {k V : Type*} [CommRing k]
    (e : SimpleEdge V) : MvPolynomial (TwistVariable V) k :=
  Sym2.lift ⟨fun u v ↦
    Twist.splitKlein (universalTwist u - universalTwist v), by
      intro u v
      exact Twist.splitKlein_sub_comm _ _⟩ e.1

/-- The coordinate dictionary: evaluating an edge polynomial is exactly the
point-set Split--Klein value of that edge. -/
theorem eval_edgePolynomial {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) =
      nullDifferenceValue Y e := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [edgePolynomial, nullDifferenceValue, Sym2.lift_mk]
      rw [eval_splitKlein, evalPolynomialTwist_sub,
        evalPolynomialTwist_universal, evalPolynomialTwist_universal]

@[simp]
theorem eval_edgePolynomial_mk {k V : Type*} [CommRing k]
    (Y : V → Twist k) (u v : V) (huv : u ≠ v) :
    eval (assignmentOfTwists Y)
        (edgePolynomial (k := k)
          ⟨s(u, v), fun h ↦ huv (Sym2.mk_isDiag_iff.mp h)⟩) =
      Twist.splitKlein (Y u - Y v) := by
  rw [eval_edgePolynomial]
  rfl

/-- The scalar edge value vanishes exactly when the existing point-set
predicate `IsNullOnEdge` holds. -/
theorem nullDifferenceValue_eq_zero_iff {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    nullDifferenceValue Y e = 0 ↔ IsNullOnEdge Y e := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v => rfl

/-- Evaluation of one edge generator vanishes exactly on its point-set edge
equation. -/
theorem eval_edgePolynomial_eq_zero_iff {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) = 0 ↔
      IsNullOnEdge Y e := by
  rw [eval_edgePolynomial, nullDifferenceValue_eq_zero_iff]

/-- The ideal generated by the selected edge quadrics. -/
def edgeIdeal {k V : Type*} [CommRing k]
    (F : SimpleEdgeSet V) : Ideal (MvPolynomial (TwistVariable V) k) :=
  Ideal.span
    (edgePolynomial (k := k) '' (F : Set (SimpleEdge V)))

/-- An ideal vanishes at an assignment when it lies in the kernel of the
corresponding evaluation homomorphism. -/
def VanishesAt {k ι : Type*} [CommRing k]
    (a : ι → k) (I : Ideal (MvPolynomial ι k)) : Prop :=
  I ≤ RingHom.ker (MvPolynomial.eval a)

/-- The zero set of the generated edge ideal is exactly the existing
`IsNullDifferenceConfiguration` predicate. -/
theorem vanishesAt_edgeIdeal_iff {k V : Type*} [CommRing k] [DecidableEq V]
    (F : SimpleEdgeSet V) (Y : V → Twist k) :
    VanishesAt (assignmentOfTwists Y) (edgeIdeal (k := k) F) ↔
      IsNullDifferenceConfiguration F Y := by
  constructor
  · intro hIdeal e he
    apply (eval_edgePolynomial_eq_zero_iff Y e).mp
    have hGenerator : edgePolynomial (k := k) e ∈ edgeIdeal (k := k) F := by
      apply Ideal.subset_span
      exact ⟨e, he, rfl⟩
    simpa [VanishesAt] using hIdeal hGenerator
  · intro hNull
    rw [VanishesAt, edgeIdeal, Ideal.span_le]
    rintro P ⟨e, he, rfl⟩
    change eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) = 0
    exact (eval_edgePolynomial_eq_zero_iff Y e).mpr (hNull e he)

/-! ## Standard homogeneity -/

theorem angularDifference_isHomogeneous_one
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (angularCoordinate (k := k) u i -
      angularCoordinate (k := k) v i).IsHomogeneous 1 := by
  simpa only [angularCoordinate] using
    (MvPolynomial.isHomogeneous_X k
      (⟨u, ⟨false, i⟩⟩ : TwistVariable V)).sub
      (MvPolynomial.isHomogeneous_X k
        (⟨v, ⟨false, i⟩⟩ : TwistVariable V))

theorem translationalDifference_isHomogeneous_one
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (translationalCoordinate (k := k) u i -
      translationalCoordinate (k := k) v i).IsHomogeneous 1 := by
  simpa only [translationalCoordinate] using
    (MvPolynomial.isHomogeneous_X k
      (⟨u, ⟨true, i⟩⟩ : TwistVariable V)).sub
      (MvPolynomial.isHomogeneous_X k
        (⟨v, ⟨true, i⟩⟩ : TwistVariable V))

theorem splitKleinDifferenceTerm_isHomogeneous_two
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (((universalTwist (k := k) u - universalTwist (k := k) v).1 i) *
      ((universalTwist (k := k) u - universalTwist (k := k) v).2 i)).IsHomogeneous 2 := by
  simpa [universalTwist, angularCoordinate, translationalCoordinate] using
    (angularDifference_isHomogeneous_one (k := k) u v i).mul
      (translationalDifference_isHomogeneous_one (k := k) u v i)

/-- Every edge generator is standard-total-degree homogeneous of degree two. -/
theorem edgePolynomial_isHomogeneous_two
    {k V : Type*} [CommRing k] (e : SimpleEdge V) :
    (edgePolynomial (k := k) e).IsHomogeneous 2 := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [edgePolynomial, Sym2.lift_mk, Twist.splitKlein, Vec3.dot]
      simpa using MvPolynomial.IsHomogeneous.sum Finset.univ
        (fun i ↦
          ((universalTwist (k := k) u - universalTwist (k := k) v).1 i) *
            ((universalTwist (k := k) u - universalTwist (k := k) v).2 i))
        2 (fun i _ ↦
          splitKleinDifferenceTerm_isHomogeneous_two (k := k) u v i)

end

end NullCellulePolynomial

end RB31E2E
