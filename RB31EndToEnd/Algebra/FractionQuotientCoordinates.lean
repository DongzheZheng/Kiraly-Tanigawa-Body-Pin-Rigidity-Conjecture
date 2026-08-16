import RB31EndToEnd.Algebra.PolynomialPrimeTrdegHeight

/-!
# Coordinate generation of a polynomial quotient function field

The fraction field of a prime quotient of a polynomial ring is generated,
as a field over the base field, by the images of the polynomial coordinate
variables.  The proof expands quotient elements polynomially and fraction
field elements by the localization universal representation.
-/

namespace RB31E2E

namespace FractionQuotientCoordinates

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The quotient-function-field coordinate family. -/
def coordinate
    {k ι : Type*} [Field k]
    (p : Ideal (MvPolynomial ι k)) [p.IsPrime] (
      i : ι) : FractionRing (MvPolynomial ι k ⧸ p) :=
  algebraMap (MvPolynomial ι k ⧸ p)
      (FractionRing (MvPolynomial ι k ⧸ p))
    (Ideal.Quotient.mk p (X i))

/-- Polynomial coordinate images generate the entire quotient function
field. -/
theorem adjoin_coordinate_eq_top
    {k ι : Type*} [Field k]
    (p : Ideal (MvPolynomial ι k)) [p.IsPrime] :
    IntermediateField.adjoin k (Set.range (coordinate p)) = ⊤ := by
  classical
  let B := MvPolynomial ι k ⧸ p
  let K := FractionRing B
  let L : IntermediateField k K :=
    IntermediateField.adjoin k (Set.range (coordinate p))
  apply top_unique
  intro z _hz
  have hpoly : ∀ f : MvPolynomial ι k,
      algebraMap B K (Ideal.Quotient.mk p f) ∈ L := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
        change algebraMap B K (algebraMap k B r) ∈ L
        rw [← IsScalarTower.algebraMap_apply k B K]
        exact L.algebraMap_mem r
    | add f g hf hg =>
        simpa using L.add_mem hf hg
    | mul_X f i hf =>
        have hXi : coordinate p i ∈ L :=
          IntermediateField.subset_adjoin k
            (Set.range (coordinate p)) ⟨i, rfl⟩
        simpa [coordinate, B, K] using L.mul_mem hf hXi
  have hquot : ∀ b : B, algebraMap B K b ∈ L := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact hpoly f
  obtain ⟨x, hx⟩ := IsLocalization.surj (nonZeroDivisors B) z
  rcases x with ⟨num, den⟩
  have hden : algebraMap B K (den : B) ≠ 0 :=
    (IsLocalization.map_units K den).ne_zero
  have hzdiv : z = algebraMap B K num / algebraMap B K (den : B) :=
    (eq_div_iff hden).2 hx
  rw [hzdiv]
  exact L.div_mem (hquot num) (hquot den)

end

end FractionQuotientCoordinates

end RB31E2E
