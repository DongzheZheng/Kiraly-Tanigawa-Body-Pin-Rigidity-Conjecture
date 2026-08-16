import RB31EndToEnd.NullCellule.WeightInitialIdeal
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.Ideal

/-!
# Filtered initial forms and a height-comparison interface

The project uses the minimum nonzero component for a nonnegative natural
weight. Mathlib's Rees algebra is currently the Rees algebra of powers of a
single ideal; it does not provide the flat one-parameter family attached to an
arbitrary weight filtration. Accordingly, this file proves the part of that
bridge which can be checked directly from the graded decomposition:

* multiplication by a weight-zero polynomial commutes with every weighted
  component;
* a nonzero weight-zero factor carries initial forms to initial forms;
* denominator clearing by such a factor gives a provenance receipt in the
  weight-initial ideal;
* a prime ideal containing products from disjoint variable pairs chooses one
  variable from every pair, and these choices remain distinct.

The last section names the flat-degeneration height comparison as an explicit
proposition.  The results in this file do not assume that proposition.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

section WeightZero

variable {k σ : Type*} [CommRing k]

set_option maxRecDepth 10000

/-- Weighted components of a product are the convolution of the weighted
components.  This is the multiplicativity law of the natural-number weight
filtration, exposed at the polynomial level. -/
theorem weightedHomogeneousComponent_mul
    (w : σ → ℕ) (f g : MvPolynomial σ k) (n : ℕ) :
    weightedHomogeneousComponent w n (f * g) =
      ∑ ij ∈ Finset.antidiagonal n,
        weightedHomogeneousComponent w ij.1 f *
          weightedHomogeneousComponent w ij.2 g := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule k w) :=
    weightedGradedAlgebra k w
  rw [← weightedDecomposition.decompose'_apply k w (f * g) n]
  change
    ((DirectSum.decompose (weightedHomogeneousSubmodule k w) (f * g)) n :
        MvPolynomial σ k) = _
  rw [DirectSum.decompose_mul,
    DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← weightedDecomposition.decompose'_apply k w f ij.1,
    ← weightedDecomposition.decompose'_apply k w g ij.2]
  rfl

/-- Initial components multiply over a domain.  In particular, the minimum
weight of a product is the sum of the two minimum weights. -/
theorem IsInitialComponent.mul [IsDomain k]
    (w : σ → ℕ) {f f₀ g g₀ : MvPolynomial σ k}
    (hf : IsInitialComponent w f f₀)
    (hg : IsInitialComponent w g g₀) :
    IsInitialComponent w (f * g) (f₀ * g₀) := by
  rcases hf with ⟨d, hfd, hf₀, hflow⟩
  rcases hg with ⟨e, hge, hg₀, hglow⟩
  refine ⟨d + e, ?_, mul_ne_zero hf₀ hg₀, ?_⟩
  · rw [weightedHomogeneousComponent_mul]
    rw [Finset.sum_eq_single (d, e)]
    · rw [hfd, hge]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = d + e := by
        simpa using (Finset.mem_antidiagonal.mp hij)
      by_cases hi : i < d
      · rw [hflow i hi, zero_mul]
      by_cases hj : j < e
      · rw [hglow j hj, mul_zero]
      exfalso
      apply hne
      apply Prod.ext <;> omega
    · simp
  · intro n hn
    rw [weightedHomogeneousComponent_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij' : i + j = n := by
      simpa using (Finset.mem_antidiagonal.mp hij)
    by_cases hi : i < d
    · rw [hflow i hi, zero_mul]
    · have hj : j < e := by omega
      rw [hglow j hj, mul_zero]

/-- Multiplication on the left by a weight-zero homogeneous polynomial
commutes with projection to every weighted component. -/
theorem weightedHomogeneousComponent_mul_left_zero
    (w : σ → ℕ) {s f : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (d : ℕ) :
    weightedHomogeneousComponent w d (s * f) =
      s * weightedHomogeneousComponent w d f := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule k w) :=
    weightedGradedAlgebra k w
  rw [← weightedDecomposition.decompose'_apply k w (s * f) d,
    ← weightedDecomposition.decompose'_apply k w f d]
  exact DirectSum.coe_decompose_mul_of_left_mem_zero
    (weightedHomogeneousSubmodule k w) (a := s) (b := f) (j := d) hs

/-- The right-handed form; it is stated separately so callers do not need to
normalize commutative products by hand. -/
theorem weightedHomogeneousComponent_mul_right_zero
    (w : σ → ℕ) {s f : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (d : ℕ) :
    weightedHomogeneousComponent w d (f * s) =
      weightedHomogeneousComponent w d f * s := by
  rw [mul_comm f s, weightedHomogeneousComponent_mul_left_zero w hs d,
    mul_comm s]

/-- A nonzero weight-zero factor preserves the exact initial degree and
multiplies the initial form. The domain assumption is used only to prevent
the displayed product from vanishing. -/
theorem IsInitialComponent.mul_left_weightZero
    [IsDomain k] (w : σ → ℕ) {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hfg : IsInitialComponent w f g) :
    IsInitialComponent w (s * f) (s * g) := by
  rcases hfg with ⟨d, hd, hg0, hlow⟩
  refine ⟨d, ?_, mul_ne_zero hs0 hg0, ?_⟩
  · rw [weightedHomogeneousComponent_mul_left_zero w hs d, hd]
  · intro e he
    rw [weightedHomogeneousComponent_mul_left_zero w hs e, hlow e he,
      mul_zero]

/-- Right multiplication by a nonzero weight-zero factor preserves an
initial component. -/
theorem IsInitialComponent.mul_right_weightZero
    [IsDomain k] (w : σ → ℕ) {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hfg : IsInitialComponent w f g) :
    IsInitialComponent w (f * s) (g * s) := by
  simpa only [mul_comm f s, mul_comm g s] using
    hfg.mul_left_weightZero w hs hs0

/-- The weight-initial ideal is monotone in the source ideal. -/
theorem weightInitialIdeal_mono
    (w : σ → ℕ) {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) :
    weightInitialIdeal w I ≤ weightInitialIdeal w J := by
  rw [weightInitialIdeal, weightInitialIdeal, Ideal.span_le]
  rintro g ⟨f, hfI, hfg⟩
  exact Ideal.subset_span ⟨f, hIJ hfI, hfg⟩

/-- Denominator-clearing receipt for localization at nonzero weight-zero
elements. If s * f lies in I and g is the initial form of f, then
s * g lies in the initial ideal of I.

This is the exact algebraic statement needed before passing to fractions; it
does not assume or claim a localization/initial-ideal equivalence. -/
theorem weightZero_denominatorClearing_mem_weightInitialIdeal
    [IsDomain k] (w : σ → ℕ) (I : Ideal (MvPolynomial σ k))
    {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hsf : s * f ∈ I) (hfg : IsInitialComponent w f g) :
    s * g ∈ weightInitialIdeal w I :=
  initialComponent_mem_weightInitialIdeal w I hsf
    (hfg.mul_left_weightZero w hs hs0)

/-- The multiplicative system of nonzero weight-zero homogeneous
polynomials. -/
def nonzeroWeightZeroSubmonoid [IsDomain k] (w : σ → ℕ) :
    Submonoid (MvPolynomial σ k) where
  carrier := {s | IsWeightedHomogeneous w s 0 ∧ s ≠ 0}
  one_mem' := ⟨isWeightedHomogeneous_one k w, one_ne_zero⟩
  mul_mem' hs ht := ⟨hs.1.mul ht.1, mul_ne_zero hs.2 ht.2⟩

@[simp]
theorem mem_nonzeroWeightZeroSubmonoid [IsDomain k]
    (w : σ → ℕ) (s : MvPolynomial σ k) :
    s ∈ nonzeroWeightZeroSubmonoid (k := k) w ↔
      IsWeightedHomogeneous w s 0 ∧ s ≠ 0 :=
  Iff.rfl

/-- Actual localization compatibility.  If `f` belongs to the extension of
`I` after inverting all nonzero weight-zero elements, then every initial form
`g` of `f` belongs to the extension of `weightInitialIdeal w I` in the same
localization.

The proof extracts a genuine denominator from mathlib's localization
membership theorem and applies the denominator-clearing receipt above. -/
theorem initialComponent_mem_localized_weightInitialIdeal
    [IsDomain k] (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k))
    {A : Type*} [CommRing A] [Algebra (MvPolynomial σ k) A]
    [IsLocalization (nonzeroWeightZeroSubmonoid (k := k) w) A]
    {f g : MvPolynomial σ k}
    (hf : algebraMap (MvPolynomial σ k) A f ∈
      I.map (algebraMap (MvPolynomial σ k) A))
    (hfg : IsInitialComponent w f g) :
    algebraMap (MvPolynomial σ k) A g ∈
      (weightInitialIdeal w I).map
        (algebraMap (MvPolynomial σ k) A) := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    (nonzeroWeightZeroSubmonoid (k := k) w) A] at hf ⊢
  obtain ⟨s, hs, hsf⟩ := hf
  exact ⟨s, hs,
    weightZero_denominatorClearing_mem_weightInitialIdeal
      w I hs.1 hs.2 hsf hfg⟩

end WeightZero

section DisjointPairs

variable {k σ ι : Type*} [CommRing k]

/-! ### Coordinate ideals -/

/-- The ideal generated by the coordinate variables named by `S`. -/
def coordinateVariableIdeal (S : Set σ) : Ideal (MvPolynomial σ k) :=
  Ideal.span (X '' S)

/-- Set the variables in `S` to zero and retain the complementary variables.
The target variable type remembers the complement membership. -/
def coordinateComplementHom (S : Set σ) :
    MvPolynomial σ k →+* MvPolynomial {x : σ // x ∉ S} k :=
  (MvPolynomial.killCompl (R := k)
    (f := fun x : {x : σ // x ∉ S} ↦ (x : σ))
    Subtype.val_injective).toRingHom

/-- A coordinate variable belongs to the coordinate ideal exactly when its
name belongs to the chosen set. -/
theorem X_mem_coordinateVariableIdeal_iff [Nontrivial k]
    (S : Set σ) (x : σ) :
    X x ∈ coordinateVariableIdeal (k := k) S ↔ x ∈ S := by
  rw [coordinateVariableIdeal, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    obtain ⟨i, hiS, hi⟩ := h (Finsupp.single x 1) (by simp [support_X])
    have hix : i = x := by
      by_contra hne
      simp [hne] at hi
    simpa [hix] using hiS
  · intro hxS m hm
    rw [support_X] at hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact ⟨x, hxS, by simp⟩

/-- The coordinate ideal is exactly the kernel of evaluation which kills
those coordinates.  This is the substantive bridge used to prove primality;
it is proved coefficientwise, rather than postulated. -/
theorem coordinateVariableIdeal_eq_ker_coordinateComplementHom
    (S : Set σ) :
    coordinateVariableIdeal (k := k) S =
      RingHom.ker (coordinateComplementHom (k := k) S) := by
  classical
  apply le_antisymm
  · rw [coordinateVariableIdeal, Ideal.span_le]
    rintro _ ⟨x, hxS, rfl⟩
    change coordinateComplementHom (k := k) S (X x) = 0
    simp [coordinateComplementHom, MvPolynomial.killCompl, hxS]
  · intro p hp
    rw [coordinateVariableIdeal, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hexists
    push Not at hexists
    let f : {x : σ // x ∉ S} → σ := fun x ↦ (x : σ)
    have hf : Function.Injective f := Subtype.val_injective
    have hmSub : (↑m.support : Set σ) ⊆ Set.range f := by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      intro hxS
      exact (Finsupp.mem_support_iff.mp hx) (hexists x hxS)
    let n : {x : σ // x ∉ S} →₀ ℕ :=
      m.comapDomain f hf.injOn
    have hmap : n.mapDomain f = m := by
      exact m.mapDomain_comapDomain f hf hmSub
    change coordinateComplementHom (k := k) S p = 0 at hp
    have hcoeff := congrArg (fun q ↦ MvPolynomial.coeff n q) hp
    have hcoeff' : MvPolynomial.coeff (n.mapDomain f) p = 0 := by
      change MvPolynomial.coeff n
        ((MvPolynomial.killCompl (R := k) (f := f) hf) p) = 0 at hcoeff
      rw [MvPolynomial.coeff_killCompl] at hcoeff
      exact hcoeff
    rw [hmap] at hcoeff'
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff'

/-- Coordinate ideals over a domain are prime: their quotient is witnessed
by the polynomial ring on the complementary variables. -/
theorem coordinateVariableIdeal_isPrime [IsDomain k] (S : Set σ) :
    (coordinateVariableIdeal (k := k) S).IsPrime := by
  rw [coordinateVariableIdeal_eq_ker_coordinateComplementHom]
  exact RingHom.ker_isPrime (coordinateComplementHom (k := k) S)

/-! ### Height of a finite coordinate ideal -/

/-- The variables among an injectively labelled finite family whose indices
occur strictly before `j`. -/
def coordinatePrefixSet {n : ℕ} (c : Fin n → σ) (j : Fin (n + 1)) : Set σ :=
  {x | ∃ i : Fin n, i.1 < j.1 ∧ c i = x}

theorem coordinatePrefixSet_mono {n : ℕ} (c : Fin n → σ)
    {j l : Fin (n + 1)} (hjl : j ≤ l) :
    coordinatePrefixSet c j ⊆ coordinatePrefixSet c l := by
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hjl, rfl⟩

/-- Successive prefix coordinate ideals are genuinely distinct. -/
theorem coordinatePrefixIdeal_lt [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c)
    {j l : Fin (n + 1)} (hjl : j < l) :
    coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) <
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) := by
  have hle :
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) ≤
        coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) := by
    exact Ideal.span_mono (Set.image_mono
      (coordinatePrefixSet_mono c hjl.le))
  refine lt_of_le_of_ne hle ?_
  let i : Fin n := ⟨j.1, by omega⟩
  have hiL : c i ∈ coordinatePrefixSet c l := by
    exact ⟨i, hjl, rfl⟩
  have hiJ : c i ∉ coordinatePrefixSet c j := by
    rintro ⟨q, hq, hqc⟩
    have hqi : q = i := hc hqc
    subst q
    exact (Nat.lt_irrefl j.1) hq
  intro heq
  have hxL : X (c i) ∈
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) :=
    (X_mem_coordinateVariableIdeal_iff
      (k := k) (coordinatePrefixSet c l) (c i)).2 hiL
  have hxJ : X (c i) ∈
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) := by
    rw [heq]
    exact hxL
  exact hiJ ((X_mem_coordinateVariableIdeal_iff
    (k := k) (coordinatePrefixSet c j) (c i)).1 hxJ)

theorem coordinatePrefixSet_last {n : ℕ} (c : Fin n → σ) :
    coordinatePrefixSet c (Fin.last n) = Set.range c := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

/-- The coordinate ideal generated by `n` distinct variables has height at
least `n`.  The proof is an explicit chain of `n + 1` prime coordinate
ideals, not a dimension formula imported from algebraic geometry. -/
theorem coordinateVariableIdeal_height_ge_card [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c) :
    (n : ℕ∞) ≤ (coordinateVariableIdeal (k := k) (Set.range c)).height := by
  let p : Fin (n + 1) → PrimeSpectrum (MvPolynomial σ k) := fun j ↦
    ⟨coordinateVariableIdeal (k := k) (coordinatePrefixSet c j),
      coordinateVariableIdeal_isPrime (k := k) (coordinatePrefixSet c j)⟩
  have hp : StrictMono p := by
    intro j l hjl
    exact coordinatePrefixIdeal_lt (k := k) c hc hjl
  let chain : LTSeries (PrimeSpectrum (MvPolynomial σ k)) :=
    LTSeries.mk n p hp
  have hchain := Order.length_le_height_last (p := chain)
  have hlast : chain.last.asIdeal =
      coordinateVariableIdeal (k := k) (Set.range c) := by
    change coordinateVariableIdeal (k := k)
      (coordinatePrefixSet c (Fin.last n)) = _
    rw [coordinatePrefixSet_last]
  haveI : (coordinateVariableIdeal (k := k) (Set.range c)).IsPrime :=
    coordinateVariableIdeal_isPrime (k := k) (Set.range c)
  have hlast' : chain.last =
      (⟨coordinateVariableIdeal (k := k) (Set.range c), inferInstance⟩ :
        PrimeSpectrum (MvPolynomial σ k)) :=
    PrimeSpectrum.ext hlast
  rw [hlast'] at hchain
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  simpa [chain] using hchain

/-- The monomial ideal generated by a family of variable products. -/
def pairedVariableIdeal (a b : ι → σ) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range fun i ↦ X (a i) * X (b i))

/-- Every named pair product belongs to its paired-variable ideal. -/
theorem pairProduct_mem_pairedVariableIdeal (a b : ι → σ) (i : ι) :
    X (a i) * X (b i) ∈ pairedVariableIdeal (k := k) a b :=
  Ideal.subset_span (Set.mem_range_self i)

/-- A prime containing the paired-variable ideal contains at least one
endpoint of every pair. -/
theorem prime_mem_left_or_right_of_pairedVariableIdeal_le
    (a b : ι → σ) (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : pairedVariableIdeal (k := k) a b ≤ P) (i : ι) :
    X (a i) ∈ P ∨ X (b i) ∈ P := by
  exact Ideal.IsPrime.mem_or_mem (I := P) inferInstance
    (hP (pairProduct_mem_pairedVariableIdeal (k := k) a b i))

/-- A convenient disjointness formulation for the two endpoint maps: no
endpoint of one named pair is equal to any endpoint of another pair, and the
two endpoints of each pair are also different. -/
def PairwiseDisjointEndpoints (a b : ι → σ) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧
    ∀ i j, a i ≠ b j

/-- From a prime cover of pair products, choose one endpoint in every pair.
Under PairwiseDisjointEndpoints, the chosen variables are still indexed
injectively, and their coordinate ideal is contained in the prime. -/
theorem exists_injective_coordinateChoice_le_prime
    (a b : ι → σ) (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hdisj : PairwiseDisjointEndpoints a b)
    (hP : pairedVariableIdeal (k := k) a b ≤ P) :
    ∃ c : ι → σ,
      Function.Injective c ∧
      (∀ i, c i = a i ∨ c i = b i) ∧
      Ideal.span (Set.range fun i ↦ X (c i)) ≤ P := by
  classical
  let c : ι → σ := fun i ↦ if X (a i) ∈ P then a i else b i
  have hcSide : ∀ i, c i = a i ∨ c i = b i := by
    intro i
    by_cases hi : X (a i) ∈ P
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  have hcP : ∀ i, X (c i) ∈ P := by
    intro i
    by_cases hi : X (a i) ∈ P
    · simp [c, hi]
    · have hir := prime_mem_left_or_right_of_pairedVariableIdeal_le
        (k := k) a b P hP i
      exact by simpa [c, hi] using hir.resolve_left hi
  refine ⟨c, ?_, hcSide, ?_⟩
  · intro i j hij
    rcases hcSide i with hia | hib <;>
      rcases hcSide j with hja | hjb
    · exact hdisj.1 (hia.symm.trans (hij.trans hja))
    · exact ((hdisj.2.2 i j) (hia.symm.trans (hij.trans hjb))).elim
    · exact ((hdisj.2.2 j i) (hja.symm.trans (hij.symm.trans hib))).elim
    · exact hdisj.2.1 (hib.symm.trans (hij.trans hjb))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hcP i

/-- The monomial ideal generated by `n` pairwise-disjoint variable products
has height at least `n`.  Every minimal prime must choose one endpoint from
each pair; the preceding explicit coordinate-prime chain then supplies the
height bound. -/
theorem pairedVariableIdeal_height_ge_card [IsDomain k] {n : ℕ}
    (a b : Fin n → σ) (hdisj : PairwiseDisjointEndpoints a b) :
    (n : ℕ∞) ≤ (pairedVariableIdeal (k := k) a b).height := by
  rw [Ideal.height]
  apply le_iInf
  intro P
  apply le_iInf
  intro hP
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  obtain ⟨c, hc, _, hcoord⟩ :=
    exists_injective_coordinateChoice_le_prime
      (k := k) a b P hdisj hP.1.2
  have himage :
      (X '' Set.range c : Set (MvPolynomial σ k)) =
        Set.range (fun i ↦ (X (c i) : MvPolynomial σ k)) := by
    ext q
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨c i, ⟨i, rfl⟩, rfl⟩
  have hcoord' :
      coordinateVariableIdeal (k := k) (Set.range c) ≤ P := by
    simpa [coordinateVariableIdeal, himage] using hcoord
  have hge := coordinateVariableIdeal_height_ge_card (k := k) c hc
  have hfinal := hge.trans (Ideal.height_mono hcoord')
  rw [Ideal.height_eq_primeHeight] at hfinal
  exact hfinal

/-- Over a Noetherian coefficient ring with finitely many ambient variables,
the preceding lower bound meets Krull's height theorem.  Hence the
pairwise-disjoint product ideal has height exactly the number of pairs. -/
theorem pairedVariableIdeal_height_eq_card
    [IsDomain k] [IsNoetherianRing k] [Finite σ] {n : ℕ}
    (a b : Fin n → σ) (hdisj : PairwiseDisjointEndpoints a b) :
    (pairedVariableIdeal (k := k) a b).height = (n : ℕ∞) := by
  let g : Fin n → MvPolynomial σ k := fun i ↦ X (a i) * X (b i)
  let cc : MvPolynomial σ k →+* k := MvPolynomial.constantCoeff
  have hker : pairedVariableIdeal (k := k) a b ≤ RingHom.ker cc := by
    rw [pairedVariableIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change cc (X (a i) * X (b i)) = 0
    simp [cc]
  have hne : pairedVariableIdeal (k := k) a b ≠ ⊤ :=
    ne_top_of_le_ne_top (RingHom.ker_ne_top cc) hker
  have hspan : (pairedVariableIdeal (k := k) a b).spanFinrank ≤ n := by
    change (Ideal.span (Set.range g)).spanFinrank ≤ n
    refine (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.finite_range g)).trans ?_
    rw [← Set.image_univ]
    simpa using Set.ncard_image_le (f := g) (s := Set.univ)
  apply le_antisymm
  · apply (Ideal.height_le_spanFinrank _ hne).trans
    exact_mod_cast hspan
  · exact pairedVariableIdeal_height_ge_card (k := k) a b hdisj

/-- A directly usable initial-ideal bridge: inclusion of a disjoint-pair
monomial ideal forces the weight-initial ideal itself to have height at least
the number of pairs.  This statement needs no flatness comparison. -/
theorem weightInitialIdeal_height_ge_card_of_pairedVariableIdeal_le
    [IsDomain k] {n : ℕ} (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k)) (a b : Fin n → σ)
    (hdisj : PairwiseDisjointEndpoints a b)
    (hpair : pairedVariableIdeal (k := k) a b ≤ weightInitialIdeal w I) :
    (n : ℕ∞) ≤ (weightInitialIdeal w I).height :=
  (pairedVariableIdeal_height_ge_card (k := k) a b hdisj).trans
    (Ideal.height_mono hpair)

/-- Membership form of the preceding theorem.  It matches local initial-form
certificates, which normally establish the pair products one at a time. -/
theorem weightInitialIdeal_height_ge_card_of_disjoint_pair_members
    [IsDomain k] {n : ℕ} (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k)) (a b : Fin n → σ)
    (hdisj : PairwiseDisjointEndpoints a b)
    (hpair : ∀ i, X (a i) * X (b i) ∈ weightInitialIdeal w I) :
    (n : ℕ∞) ≤ (weightInitialIdeal w I).height := by
  apply weightInitialIdeal_height_ge_card_of_pairedVariableIdeal_le
    (k := k) w I a b hdisj
  rw [pairedVariableIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hpair i

end DisjointPairs

/-! ## Height-comparison interface

The proposition below states the height comparison associated with a flat
weighted Rees family.  It is defined here without being assumed by any
theorem in this file.
-/

section HeightInterface

variable {k σ : Type*} [CommRing k]

/-- Height monotonicity from a weighted initial ideal to its source ideal. -/
def WeightInitialHeightMonotone : Prop :=
  ∀ (w : σ → ℕ) (I : Ideal (MvPolynomial σ k)),
    (weightInitialIdeal w I).height ≤ I.height

end HeightInterface

end

end NullCellulePolynomial

end RB31E2E
