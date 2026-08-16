import RB31EndToEnd.Algebra.ComplexRealSpecialization
import RB31EndToEnd.Linear.PinFibres

/-!
# A nonzero polynomial certificate for three collinear pins

The high-multiplicity branch of the incidence proof is not merely called
"nongeneric": three specified pin occurrences satisfy an explicit nonzero
integer polynomial.  Keeping the occurrence labels in the variable type is
the provenance needed to know that the certificate is genuinely nonzero.
-/

namespace RB31E2E

namespace PinCollinearity

noncomputable section

open MvPolynomial

/-- Three coordinates for every pin occurrence. -/
abbrev Variable (E : Type*) := E × Fin 3

def coordinate {E : Type*} (e : E) (i : Fin 3) :
    MvPolynomial (Variable E) ℤ :=
  X (e, i)

/-- One `2×2` minor of the two displacement vectors from `e₀`. -/
def minor01 {E : Type*} (e₀ e₁ e₂ : E) :
    MvPolynomial (Variable E) ℤ :=
  (coordinate e₁ 0 - coordinate e₀ 0) *
      (coordinate e₂ 1 - coordinate e₀ 1) -
    (coordinate e₁ 1 - coordinate e₀ 1) *
      (coordinate e₂ 0 - coordinate e₀ 0)

def assignmentOfPins {k E : Type*} [CommRing k]
    (p : E → Vec3 k) : Variable E → k :=
  fun ei ↦ p ei.1 ei.2

theorem eval_minor01 {k E : Type*} [CommRing k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) =
      (p e₁ 0 - p e₀ 0) * (p e₂ 1 - p e₀ 1) -
        (p e₁ 1 - p e₀ 1) * (p e₂ 0 - p e₀ 0) := by
  simp [minor01, coordinate, assignmentOfPins]

/-- Affine collinearity with a retained direction witness. -/
def Collinear {k : Type*} [CommRing k] (p₀ p₁ p₂ : Vec3 k) : Prop :=
  ∃ (d : Vec3 k) (c₁ c₂ : k),
    p₁ - p₀ = c₁ • d ∧ p₂ - p₀ = c₂ • d

theorem minor01_eq_zero_of_collinear {k E : Type*} [CommRing k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E)
    (hcol : Collinear (p e₀) (p e₁) (p e₂)) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) = 0 := by
  obtain ⟨d, c₁, c₂, h₁, h₂⟩ := hcol
  rw [eval_minor01]
  have h₁0 := congrFun h₁ 0
  have h₁1 := congrFun h₁ 1
  have h₂0 := congrFun h₂ 0
  have h₂1 := congrFun h₂ 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h₁0 h₁1 h₂0 h₂1
  rw [h₁0, h₁1, h₂0, h₂1]
  ring

/-- A common nonzero relative twist forces the polynomial certificate to
vanish on any three compatible pins. -/
theorem minor01_eq_zero_of_common_twist {k E : Type*} [Field k]
    (p : E → Vec3 k) (e₀ e₁ e₂ : E) (Y : Twist k) (hY : Y ≠ 0)
    (h₀ : Twist.eval Y (p e₀) = 0)
    (h₁ : Twist.eval Y (p e₁) = 0)
    (h₂ : Twist.eval Y (p e₂) = 0) :
    eval₂ (Int.castRingHom k) (assignmentOfPins p) (minor01 e₀ e₁ e₂) = 0 := by
  apply minor01_eq_zero_of_collinear p e₀ e₁ e₂
  obtain ⟨c₁, c₂, hc₁, hc₂⟩ :=
    Twist.three_pin_solutions_collinear_of_ne_zero Y
      (p e₀) (p e₁) (p e₂) hY h₀ h₁ h₂
  exact ⟨Y.1, c₁, c₂, hc₁, hc₂⟩

/-- The test assignment `e₁ ↦ (1,0,0)`, `e₂ ↦ (0,1,0)`,
`e₀ ↦ 0` witnesses that the minor polynomial is not zero. -/
def testAssignment {E : Type*} [DecidableEq E] (e₁ e₂ : E) :
    Variable E → ℤ
  | (e, i) =>
      if e = e₁ ∧ i = 0 then 1
      else if e = e₂ ∧ i = 1 then 1
      else 0

theorem eval_testAssignment_minor01 {E : Type*} [DecidableEq E]
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂)
    (h₁₂ : e₁ ≠ e₂) :
    eval (testAssignment e₁ e₂) (minor01 e₀ e₁ e₂) = 1 := by
  simp [minor01, coordinate, testAssignment, h₀₁, h₀₂, h₁₂,
    Ne.symm h₁₂]

theorem minor01_ne_zero {E : Type*} [DecidableEq E]
    {e₀ e₁ e₂ : E} (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂)
    (h₁₂ : e₁ ≠ e₂) :
    minor01 e₀ e₁ e₂ ≠ 0 := by
  intro hzero
  have := eval_testAssignment_minor01 h₀₁ h₀₂ h₁₂
  rw [hzero] at this
  simp at this

end

end PinCollinearity

end RB31E2E
