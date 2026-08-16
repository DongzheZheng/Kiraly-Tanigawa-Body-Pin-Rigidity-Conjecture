import RB31EndToEnd.Algebra.HomogeneousChartContradiction

/-!
# Homogeneous contradiction on a provenance denominator

The one-coordinate chart theorem is too narrow for a distinctness chart:
excluding every unwanted equality component requires a finite product of
provenance-labelled twist differences.  This file replaces `X i` by an
arbitrary polynomial `s` in the irrelevant ideal.

If a homogeneous prime avoids `s`, then it is strictly below the irrelevant
ideal, because `s` belongs to the latter.  Hence its height is strictly less
than the number of twist variables.  The same homogeneous-core and prime-
avoidance argument as for a single coordinate then produces a concrete
receipt `s ^ m ∈ J`.

No assertion about which incidence denominator has the required height is
made here.  This is only the reusable commutative-algebra mechanism needed
once a provenance chart supplies that height.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- A homogeneous prime avoiding any specified member of the irrelevant
ideal has height strictly below the number of ambient variables. -/
theorem homogeneousPrime_height_lt_of_irrelevant_mem_not_mem
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hsP : s ∉ P) :
    P.height < (n : ℕ∞) := by
  have hle : P ≤ finiteIrrelevantIdeal (k := k) n :=
    homogeneousIdeal_le_finiteIrrelevantIdeal P
      Ideal.IsPrime.ne_top' hPhom
  have hlt : P < finiteIrrelevantIdeal (k := k) n := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hsP
    rw [heq]
    exact hsIrrelevant
  rw [← finiteIrrelevantIdeal_height (k := k) n]
  exact Ideal.height_strict_mono_of_is_prime hlt

/-- If every homogeneous prime over `J` that avoids a provenance
denominator has full ambient height, then no prime over `J` can avoid that
denominator. -/
theorem not_exists_prime_over_avoiding_denominator_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ¬ ∃ P : Ideal (MvPolynomial (Fin n) k),
      P.IsPrime ∧ J ≤ P ∧ s ∉ P := by
  rintro ⟨P, hPprime, hJP, hsP⟩
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
  have hsQ : s ∉ Q := by
    intro hs
    apply hsP
    exact P.toIdeal_homogeneousCore_le _ hs
  exact (not_lt_of_ge (hheight Q hQprime hQhom hJQ hsQ))
    (homogeneousPrime_height_lt_of_irrelevant_mem_not_mem
      (k := k) Q hQhom s hsIrrelevant hsQ)

/-- The full-height condition on the principal provenance chart gives a
finite saturation receipt in the original homogeneous ideal. -/
theorem exists_denominator_pow_mem_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ∃ m : ℕ, s ^ m ∈ J := by
  by_contra hpow
  have hnoPow : ∀ m : ℕ, s ^ m ∉ J := by
    intro m hm
    exact hpow ⟨m, hm⟩
  have hdisjoint :
      Disjoint (J : Set (MvPolynomial (Fin n) k))
        (Submonoid.powers s : Set (MvPolynomial (Fin n) k)) := by
    rw [Set.disjoint_left]
    intro f hfJ hfPow
    change f ∈ Submonoid.powers s at hfPow
    rw [Submonoid.mem_powers_iff] at hfPow
    obtain ⟨m, rfl⟩ := hfPow
    exact hnoPow m hfJ
  obtain ⟨P, hPprime, hJP, hPdisjoint⟩ :=
    J.exists_le_prime_disjoint (Submonoid.powers s) hdisjoint
  have hsP : s ∉ P := by
    intro hs
    exact Set.disjoint_left.mp hPdisjoint hs
      (Submonoid.mem_powers s)
  exact
    (not_exists_prime_over_avoiding_denominator_of_homogeneousPrime_height
      (k := k) J hJhom s hsIrrelevant hheight)
      ⟨P, hPprime, hJP, hsP⟩

/-- Radical form of the provenance-denominator receipt. -/
theorem denominator_mem_radical_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    s ∈ J.radical := by
  rw [Ideal.mem_radical_iff]
  exact exists_denominator_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom s hsIrrelevant hheight

/-- Every algebra in which the provenance denominator becomes a unit sees
the homogeneous chart ideal as the unit ideal. -/
theorem map_eq_top_of_denominator_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height)
    {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin n) k) S]
    (hunit : IsUnit
      (algebraMap (MvPolynomial (Fin n) k) S s)) :
    Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J = ⊤ := by
  obtain ⟨m, hm⟩ :=
    exists_denominator_pow_mem_of_homogeneousPrime_height
      (k := k) J hJhom s hsIrrelevant hheight
  have hmapped :
      algebraMap (MvPolynomial (Fin n) k) S (s ^ m) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J :=
    Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) k) S) hm
  have hmappedUnit :
      IsUnit (algebraMap (MvPolynomial (Fin n) k) S (s ^ m)) := by
    rw [map_pow]
    exact hunit.pow m
  exact (Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J).eq_top_of_isUnit_mem
    hmapped hmappedUnit

end

end NullCellulePolynomial

end RB31E2E
