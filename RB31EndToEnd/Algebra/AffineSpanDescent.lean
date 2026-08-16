import RB31EndToEnd.Algebra.AlgebraicIndependentAffine
import RB31EndToEnd.Linear.FiniteFamilyBaseChange

/-!
# Descent from an affine-generic scalar extension of a row space

Let `W` be a row space over a field `L`, and extend all its rows
coordinatewise to a field `K`.  If

`constant + ∑ j, x j • coefficient j`

belongs to the extended row space and the finite family `x` is
algebraically independent over `L`, then the constant term and every
coefficient already belong to `W` over `L`.

The proof is literal coefficient comparison.  A coefficient outside `W`
is separated by an `L`-linear functional.  We extend that functional
coordinatewise to `K`; it kills the extended row space and produces an
affine-linear relation among `1` and the `x j`.  The independently proved
`option_one_linearIndependent` theorem then gives the contradiction.
-/

namespace RB31E2E

namespace AffineSpanDescent

noncomputable section

open Set Submodule

variable {L K I C J : Type*}
  [Field L] [Field K] [Algebra L K]
  [Fintype I] [DecidableEq I]
  [Fintype C] [DecidableEq C]

/-- Coordinatewise scalar extension of a linear functional on a finite
function space. -/
def extendLinearFunctional (phi : (I → L) →ₗ[L] L) :
    (I → K) →ₗ[K] K where
  toFun y := ∑ i : I,
    y i * algebraMap L K (phi (Pi.single i 1))
  map_add' y z := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

/-- On a vector defined over `L`, the extended functional is just the
image of the original functional. -/
@[simp]
theorem extendLinearFunctional_mapVector
    (phi : (I → L) →ₗ[L] L) (y : I → L) :
    extendLinearFunctional (K := K) phi
        (FiniteFamilyBaseChange.mapVector (K := K) y) =
      algebraMap L K (phi y) := by
  have hy : y = ∑ i : I,
      y i • (Pi.single i (1 : L) : I → L) := by
    funext j
    simp [Pi.single_apply]
  have hphi : phi y =
      ∑ i : I, y i * phi (Pi.single i (1 : L) : I → L) := by
    calc
      phi y = phi (∑ i : I,
          y i • (Pi.single i (1 : L) : I → L)) := congrArg phi hy
      _ = ∑ i : I,
          phi (y i • (Pi.single i (1 : L) : I → L)) := by
            apply map_sum
      _ = ∑ i : I,
          y i * phi (Pi.single i (1 : L) : I → L) := by
        simp only [map_smul, smul_eq_mul]
  change (∑ i : I,
      algebraMap L K (y i) *
        algebraMap L K (phi (Pi.single i (1 : L) : I → L))) =
    algebraMap L K (phi y)
  rw [hphi, map_sum]
  simp only [map_mul]

/-- The scalar-extended functional kills the scalar-extended span of every
row killed by the original functional. -/
theorem mappedSpan_le_extendLinearFunctional_ker
    (rows : J → I → L) (phi : (I → L) →ₗ[L] L)
    (hkill : span L (Set.range rows) ≤ LinearMap.ker phi) :
    span K (Set.range (fun j ↦
        FiniteFamilyBaseChange.mapVector (K := K) (rows j))) ≤
      LinearMap.ker (extendLinearFunctional (K := K) phi) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change extendLinearFunctional (K := K) phi
      (FiniteFamilyBaseChange.mapVector (K := K) (rows j)) = 0
  rw [extendLinearFunctional_mapVector]
  have hrowZero : phi (rows j) = 0 :=
    hkill (Submodule.subset_span ⟨j, rfl⟩)
  simp [hrowZero]

omit [DecidableEq C] in
/-- Every affine coefficient descends to the original row space.  `none`
selects the constant term and `some j` selects the coefficient of `x j`. -/
theorem affineCoefficient_mem_span
    (rows : J → I → L)
    (x : C → K) (hx : AlgebraicIndependent L x)
    (constant : I → L) (coefficient : C → I → L)
    (hmem :
      FiniteFamilyBaseChange.mapVector (K := K) constant +
          ∑ j : C, x j •
            FiniteFamilyBaseChange.mapVector (K := K) (coefficient j) ∈
        span K (Set.range (fun r ↦
          FiniteFamilyBaseChange.mapVector (K := K) (rows r))))
    (o : Option C) :
    o.casesOn' constant coefficient ∈ span L (Set.range rows) := by
  let W : Submodule L (I → L) := span L (Set.range rows)
  let z : I → L := o.casesOn' constant coefficient
  by_contra hz
  have hzW : z ∉ W := by simpa [W, z] using hz
  obtain ⟨phi, hphiz, hkill⟩ :=
    Submodule.exists_le_ker_of_notMem hzW
  let phiK : (I → K) →ₗ[K] K := extendLinearFunctional (K := K) phi
  have hzero : phiK
      (FiniteFamilyBaseChange.mapVector (K := K) constant +
        ∑ j : C, x j •
          FiniteFamilyBaseChange.mapVector (K := K) (coefficient j)) = 0 := by
    exact (mappedSpan_le_extendLinearFunctional_ker
      (K := K) rows phi hkill) hmem
  have hrelation :
      algebraMap L K (phi constant) +
          ∑ j : C, x j * algebraMap L K (phi (coefficient j)) = 0 := by
    change extendLinearFunctional (K := K) phi
      (FiniteFamilyBaseChange.mapVector (K := K) constant +
        ∑ j : C, x j •
          FiniteFamilyBaseChange.mapVector (K := K) (coefficient j)) = 0
      at hzero
    simpa only [map_add, map_sum, map_smul,
      extendLinearFunctional_mapVector, smul_eq_mul] using hzero
  let affineVector : Option C → K :=
    fun q ↦ q.casesOn' (1 : K) x
  let affineCoefficient : Option C → L :=
    fun q ↦ q.casesOn' (phi constant) (fun j ↦ phi (coefficient j))
  have hsum : ∑ q : Option C,
      affineCoefficient q • affineVector q = 0 := by
    simpa [affineVector, affineCoefficient, Algebra.smul_def, mul_comm]
      using hrelation
  have hLI : LinearIndependent L affineVector := by
    simpa [affineVector] using
      (AlgebraicIndependentAffine.option_one_linearIndependent x hx)
  have hcoefficientZero : ∀ q : Option C, affineCoefficient q = 0 :=
    (Fintype.linearIndependent_iff.mp hLI) affineCoefficient hsum
  have hoZero := hcoefficientZero o
  apply hphiz
  cases o with
  | none => simpa [z, affineCoefficient] using hoZero
  | some j => simpa [z, affineCoefficient] using hoZero

omit [DecidableEq C] in
/-- Bundled form: the constant term and all variable coefficients descend
simultaneously. -/
theorem affineCoefficients_mem_span
    (rows : J → I → L)
    (x : C → K) (hx : AlgebraicIndependent L x)
    (constant : I → L) (coefficient : C → I → L)
    (hmem :
      FiniteFamilyBaseChange.mapVector (K := K) constant +
          ∑ j : C, x j •
            FiniteFamilyBaseChange.mapVector (K := K) (coefficient j) ∈
        span K (Set.range (fun r ↦
          FiniteFamilyBaseChange.mapVector (K := K) (rows r)))) :
    constant ∈ span L (Set.range rows) ∧
      ∀ j, coefficient j ∈ span L (Set.range rows) := by
  constructor
  · exact affineCoefficient_mem_span rows x hx constant coefficient hmem none
  · intro j
    exact affineCoefficient_mem_span rows x hx constant coefficient hmem (some j)

end

end AffineSpanDescent

end RB31E2E
