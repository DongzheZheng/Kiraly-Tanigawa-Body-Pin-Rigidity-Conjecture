import RB31EndToEnd.Algebra.HomogeneousPrimeChartHeight
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Maximal

/-!
# The homogeneous-chart contradiction

This file closes the abstract elimination step at the end of a normalized
homogeneous chart.  Let `J` be a homogeneous ideal in a polynomial ring in
`n` variables and fix a coordinate `X i`.  Suppose that every homogeneous
prime over `J` which misses `X i` has height at least `n`.

There can then be no (even nonhomogeneous) prime over `J` which misses
`X i`.  Indeed, the homogeneous core of such a prime is again prime, still
contains `J`, and still misses `X i`; the height lower bound contradicts the
strict chart-height bound proved in `HomogeneousPrimeChartHeight`.

Prime existence disjoint from the powers of `X i` then gives the concrete
elimination certificate `X i ^ m ∈ J` for some `m`.  Consequently every
algebra chart in which `X i` becomes a unit sends `J` to the top ideal.

No incidence-specific dimension or null-cellule height assertion enters
this argument.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- If every homogeneous prime over `J` and avoiding `X i` has height at
least the number of variables, then no prime over `J` can avoid `X i`.

The input prime is not assumed homogeneous.  Passing to its homogeneous
core is what retains the homogeneous provenance of `J` while making the
chart-height theorem applicable. -/
theorem not_exists_prime_over_avoiding_X_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ¬ ∃ P : Ideal (MvPolynomial (Fin n) k),
      P.IsPrime ∧ J ≤ P ∧ X i ∉ P := by
  rintro ⟨P, hPprime, hJP, hiP⟩
  let Q : Ideal (MvPolynomial (Fin n) k) :=
    (P.homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin n) k)).toIdeal
  have hQprime : Q.IsPrime := by
    dsimp [Q]
    exact hPprime.homogeneousCore
  letI : Q.IsPrime := hQprime
  have hQhom : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k) := by
    dsimp [Q]
    exact HomogeneousIdeal.isHomogeneous _
  have hJQ : J ≤ Q := by
    dsimp [Q]
    exact hJhom.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono _ hJP)
  have hiQ : X i ∉ Q := by
    intro hi
    apply hiP
    exact P.toIdeal_homogeneousCore_le _ hi
  exact (not_lt_of_ge (hheight Q hQprime hQhom hJQ hiQ))
    (homogeneousPrime_height_lt_of_X_not_mem
      (k := k) Q hQhom i hiQ)

/-- Under the same chart-height hypothesis, some power of the selected
coordinate belongs to `J`.  This is the concrete finite certificate that
the principal open chart `D(X i)` has empty intersection with `V(J)`. -/
theorem exists_X_pow_mem_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ∃ m : ℕ, X i ^ m ∈ J := by
  by_contra hpow
  have hnoPow : ∀ m : ℕ, X i ^ m ∉ J := by
    intro m hm
    exact hpow ⟨m, hm⟩
  have hdisjoint :
      Disjoint (J : Set (MvPolynomial (Fin n) k))
        (Submonoid.powers (X i : MvPolynomial (Fin n) k) :
          Set (MvPolynomial (Fin n) k)) := by
    rw [Set.disjoint_left]
    intro f hfJ hfPow
    change f ∈ Submonoid.powers
      (X i : MvPolynomial (Fin n) k) at hfPow
    rw [Submonoid.mem_powers_iff] at hfPow
    obtain ⟨m, rfl⟩ := hfPow
    exact hnoPow m hfJ
  obtain ⟨P, hPprime, hJP, hPdisjoint⟩ :=
    J.exists_le_prime_disjoint
      (Submonoid.powers (X i : MvPolynomial (Fin n) k)) hdisjoint
  have hiP : X i ∉ P := by
    intro hi
    exact Set.disjoint_left.mp hPdisjoint hi
      (Submonoid.mem_powers (X i : MvPolynomial (Fin n) k))
  exact
    (not_exists_prime_over_avoiding_X_of_homogeneousPrime_height
      (k := k) J hJhom i hheight) ⟨P, hPprime, hJP, hiP⟩

/-- Radical form of the same elimination conclusion. -/
theorem X_mem_radical_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    X i ∈ J.radical := by
  rw [Ideal.mem_radical_iff]
  exact exists_X_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom i hheight

/-- Any target algebra in which the chosen coordinate is a unit sees `J`
as the unit ideal.  In particular this applies to localization away from
`X i`, without coupling the theorem to a particular localization model. -/
theorem map_eq_top_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height)
    {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin n) k) S]
    (hunit : IsUnit
      (algebraMap (MvPolynomial (Fin n) k) S (X i))) :
    Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J = ⊤ := by
  obtain ⟨m, hm⟩ := exists_X_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom i hheight
  have hmapped :
      algebraMap (MvPolynomial (Fin n) k) S (X i ^ m) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J :=
    Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) k) S) hm
  have hmappedUnit :
      IsUnit (algebraMap (MvPolynomial (Fin n) k) S (X i ^ m)) := by
    rw [map_pow]
    exact hunit.pow m
  exact (Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J).eq_top_of_isUnit_mem
    hmapped hmappedUnit

end

end NullCellulePolynomial

end RB31E2E
