import RB31EndToEnd.Combinatorics.BodyPinSparseSkeleton
import RB31EndToEnd.Incidence.FiniteBadCover
import RB31EndToEnd.Incidence.TripleBundleCertificate
import RB31EndToEnd.Linear.PinFibres
import RB31EndToEnd.TargetReduction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Fixed partitions with bundles of size one or two

For an exact equality partition whose nonempty crossing bundles have size one
or two, a uniform properness statement for sparse Split--Klein null incidence
systems supplies the nonzero integer polynomial used by `FiniteBadCover`.

In particular, no certificate for a body--pin partition is stored in an
input structure or definition.  The polynomial is obtained only after:

* extracting the `(2,2)`-sparse null skeleton from the literal partition
  condition;
* identifying its edge provenance with actual crossing pin occurrences;
* transporting an exact bad motion to an injective configuration on the
  finite type of equality blocks; and
* applying the single, body--pin-independent properness principle below.

The properness principle is defined as a proposition.  Theorems that use it
state it explicitly as a premise.
-/

namespace RB31E2E

namespace SparseNullIncidence

noncomputable section

 /-- Point-set incidence semantics used by the elimination statement.  The
vertex twists must be pairwise distinct, and every selected occurrence is a
zero of its nonzero relative twist. -/
def IsIncidenceRealization {V E : Type*} [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) : Prop :=
  Function.Injective Y ∧
    ∀ e : active,
      Twist.eval (Y (src e.1) - Y (dst e.1)) (p e.1) = 0

/-! ## Explicit finite charts for the incidence fibres -/

/-- Ground at `root` and then apply one common scalar.  Pin equations depend
only on differences, so this is the point-set representative used by the
finite normalization charts. -/
def groundAndScale {k V : Type*} [Field k]
    (Y : V → Twist k) (root : V) (a : k) : V → Twist k :=
  fun v ↦ a • (Y v - Y root)

@[simp]
theorem groundAndScale_root {k V : Type*} [Field k]
    (Y : V → Twist k) (root : V) (a : k) :
    groundAndScale Y root a root = 0 := by
  simp [groundAndScale]

/-- Grounding and nonzero common scaling preserve the exact distinct
incidence realization, with the same provenance-labelled pin placement. -/
theorem IsIncidenceRealization.groundAndScale
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (root : V) {a : ℝ} (ha : a ≠ 0) :
    IsIncidenceRealization src dst active p
      (SparseNullIncidence.groundAndScale Y root a) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    apply hY.1
    have huv' : Y u - Y root = Y v - Y root :=
      (smul_twist_eq_smul_twist_iff ha _ _).mp huv
    have := congrArg (fun Z : Twist ℝ ↦ Z + Y root) huv'
    simpa only [sub_add_cancel] using this
  · intro e
    have he := congrArg (fun z : Vec3 ℝ ↦ a • z) (hY.2 e)
    have hdiff :
        SparseNullIncidence.groundAndScale Y root a (src e.1) -
            SparseNullIncidence.groundAndScale Y root a (dst e.1) =
          a • (Y (src e.1) - Y (dst e.1)) := by
      simp only [SparseNullIncidence.groundAndScale]
      module
    rw [hdiff]
    simpa [Twist.eval, Vec3.cross_smul_left] using he

/-- One of the six provenance coordinates detects every nonzero twist. -/
theorem exists_twistCoordinate_ne_zero {k : Type*} [Field k]
    {Z : Twist k} (hZ : Z ≠ 0) :
    ∃ c : GroundedTwistPolynomial.TwistCoordinate,
      GroundedTwistPolynomial.twistCoordinates Z c ≠ 0 := by
  by_contra h
  push Not at h
  apply hZ
  apply GroundedTwistPolynomial.twistCoordinates.injective
  funext c
  simpa using h c

/-- A chosen nonzero grounded coordinate can be normalized to `1`.  Together
with `groundAndScale`, this replaces the free common `G_m` orbit by finitely
many explicit affine charts. -/
theorem exists_grounded_normalization_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    {root other : V} (hne : other ≠ root) :
    ∃ c : GroundedTwistPolynomial.TwistCoordinate, ∃ a : ℝ,
      a ≠ 0 ∧
      GroundedTwistPolynomial.twistCoordinates
          (groundAndScale Y root a other) c = 1 ∧
      IsIncidenceRealization src dst active p
        (groundAndScale Y root a) := by
  have hDifference : Y other - Y root ≠ 0 := by
    exact sub_ne_zero.mpr (hY.1.ne hne)
  obtain ⟨c, hc⟩ := exists_twistCoordinate_ne_zero hDifference
  let z : ℝ := GroundedTwistPolynomial.twistCoordinates
    (Y other - Y root) c
  refine ⟨c, z⁻¹, inv_ne_zero hc, ?_, hY.groundAndScale root (inv_ne_zero hc)⟩
  change GroundedTwistPolynomial.twistCoordinates
      (z⁻¹ • (Y other - Y root)) c = 1
  rw [map_smul]
  change z⁻¹ * z = 1
  exact inv_mul_cancel₀ hc

/-- The stationary pin written in the angular-coordinate chart `i`.  The
coordinate `c` is free; the other two coordinates are rational expressions
in the relative twist and `c`. -/
def stationaryPinChart {k : Type*} [Field k]
    (Z : Twist k) (i : Fin 3) (c : k) : Vec3 k :=
  if _hi₀ : i = 0 then
    ![c,
      (Z.1 1 * c - Z.2 2) / Z.1 0,
      (Z.2 1 + Z.1 2 * c) / Z.1 0]
  else if _hi₁ : i = 1 then
    ![(Z.2 2 + Z.1 0 * c) / Z.1 1,
      c,
      (Z.1 2 * c - Z.2 0) / Z.1 1]
  else
    ![(Z.1 0 * c - Z.2 1) / Z.1 2,
      (Z.2 0 + Z.1 1 * c) / Z.1 2,
      c]

/-- Exact one-free-parameter formula for a stationary pin on an angular
coordinate chart.  This formula supplies the field-generation step for the
universal coordinate ring. -/
theorem eq_stationaryPinChart_of_eval_eq_zero
    {k : Type*} [Field k] (Z : Twist k) (p : Vec3 k)
    (i : Fin 3) (hi : Z.1 i ≠ 0) (hp : Twist.eval Z p = 0) :
    p = stationaryPinChart Z i (p i) := by
  have h₀ := congrFun hp (0 : Fin 3)
  have h₁ := congrFun hp (1 : Fin 3)
  have h₂ := congrFun hp (2 : Fin 3)
  simp [Twist.eval, Vec3.cross] at h₀ h₁ h₂
  fin_cases i
  · change Z.1 0 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₂
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₁
  · change Z.1 1 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₂
    · simp [stationaryPinChart]
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₀
  · change Z.1 2 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₁
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₀
    · simp [stationaryPinChart]

/-- The finite generating set for one angular pin chart: the six relative
twist coordinates and the single free pin coordinate. -/
def pinChartGeneratorSet (Z : Twist ℝ) (p : Vec3 ℝ) (i : Fin 3) : Set ℝ :=
  Set.range (GroundedTwistPolynomial.twistCoordinates Z) ∪ {p i}

/-- Field-generation form of `eq_stationaryPinChart_of_eval_eq_zero`.
Every pin coordinate lies in the field generated over `ℚ` by the six
relative-twist coordinates and one free pin coordinate.  This is the exact
input required for a transcendence-degree count on a universal chart; it is
strictly stronger than a pointwise dimension slogan. -/
theorem pinCoordinate_mem_adjoin_of_eval_eq_zero
    (Z : Twist ℝ) (p : Vec3 ℝ) (i j : Fin 3)
    (hi : Z.1 i ≠ 0) (hp : Twist.eval Z p = 0) :
    p j ∈ IntermediateField.adjoin ℚ (pinChartGeneratorSet Z p i) := by
  let K : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ (pinChartGeneratorSet Z p i)
  have hAngular (r : Fin 3) : Z.1 r ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inl ⟨⟨false, r⟩, rfl⟩
  have hTranslational (r : Fin 3) : Z.2 r ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inl ⟨⟨true, r⟩, rfl⟩
  have hFree : p i ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inr (Set.mem_singleton _)
  have hEq := eq_stationaryPinChart_of_eval_eq_zero Z p i hi hp
  rw [hEq]
  fin_cases i <;> fin_cases j
  all_goals simp [stationaryPinChart]
  all_goals first
    | exact hFree
    | exact K.div_mem
        (K.sub_mem (hAngular _) (hTranslational _)) (hAngular _)
    | exact K.div_mem
        (K.add_mem (hTranslational _) (K.mul_mem (hAngular _) hFree))
        (hAngular _)
    | exact K.div_mem
        (K.sub_mem (K.mul_mem (hAngular _) hFree) (hTranslational _))
        (hAngular _)

/-- Every selected incidence occurrence belongs to one of the three angular
charts, and its whole pin position is generated by the relative twist and
one retained pin coordinate. -/
theorem IsIncidenceRealization.exists_angular_pin_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 ∧
      p e.1 = stationaryPinChart
        (Y (src e.1) - Y (dst e.1)) i (p e.1 i) := by
  let Z : Twist ℝ := Y (src e.1) - Y (dst e.1)
  have hZ : Z ≠ 0 := sub_ne_zero.mpr (hY.1.ne (hLoop e.1 e.2))
  have hAngular : Z.1 ≠ 0 :=
    Twist.angular_ne_zero_of_ne_zero_of_eval_eq_zero Z (p e.1) hZ (hY.2 e)
  have hi : ∃ i : Fin 3, Z.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply hAngular
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, hi,
    eq_stationaryPinChart_of_eval_eq_zero Z (p e.1) i hi (hY.2 e)⟩

/-- Field-generation packet for one selected occurrence.  The angular chart
is chosen from the actual nonzero relative twist, and all three pin
coordinates then lie in the field generated by that twist and one free pin
coordinate. -/
theorem IsIncidenceRealization.exists_angular_pin_generation_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 ∧
      ∀ j : Fin 3,
        p e.1 j ∈ IntermediateField.adjoin ℚ
          (pinChartGeneratorSet
            (Y (src e.1) - Y (dst e.1)) (p e.1) i) := by
  obtain ⟨i, hi, _⟩ := hY.exists_angular_pin_chart hLoop e
  refine ⟨i, hi, ?_⟩
  intro j
  exact pinCoordinate_mem_adjoin_of_eval_eq_zero
    (Y (src e.1) - Y (dst e.1)) (p e.1) i j hi (hY.2 e)

/-- Global generators after choosing one angular chart per active
occurrence: all twist coordinates, one free coordinate for each active pin,
and all three coordinates of every inactive pin. -/
def incidenceChartGeneratorSet {V E : Type*} [DecidableEq E]
    (Y : V → Twist ℝ) (p : E → Vec3 ℝ) (active : Finset E)
    (chart : active → Fin 3) : Set ℝ :=
  Set.range (fun vc : V × GroundedTwistPolynomial.TwistCoordinate ↦
      GroundedTwistPolynomial.twistCoordinates (Y vc.1) vc.2) ∪
    Set.range (fun e : active ↦ p e.1 (chart e)) ∪
    Set.range (fun ej : {e : E // e ∉ active} × Fin 3 ↦
      p ej.1.1 ej.2)

/-- Simultaneous field-generation theorem for an entire incidence
realization.  This is the rigorous point-set/field bridge behind the count
"one free coordinate per crossing pin, three per inactive pin".  It still
does not infer a uniform eliminated polynomial; that final passage belongs
to the universal coordinate algebra in `PropernessPrinciple`. -/
theorem IsIncidenceRealization.exists_global_generation_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    ∃ chart : active → Fin 3,
      (∀ e : active,
        (Y (src e.1) - Y (dst e.1)).1 (chart e) ≠ 0) ∧
      ∀ (e : E) (j : Fin 3),
        p e j ∈ IntermediateField.adjoin ℚ
          (incidenceChartGeneratorSet Y p active chart) := by
  have hChart : ∀ e : active, ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 := by
    intro e
    obtain ⟨i, hi, _⟩ := hY.exists_angular_pin_chart hLoop e
    exact ⟨i, hi⟩
  choose chart hchart using hChart
  refine ⟨chart, hchart, ?_⟩
  intro e j
  let K : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ
      (incidenceChartGeneratorSet Y p active chart)
  by_cases he : e ∈ active
  · let e' : active := ⟨e, he⟩
    let Z : Twist ℝ := Y (src e) - Y (dst e)
    have hSmallLe :
        IntermediateField.adjoin ℚ
            (pinChartGeneratorSet Z (p e) (chart e')) ≤ K := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨c, rfl⟩ := hx
        rcases c with ⟨b, r⟩
        have hSrc :
            GroundedTwistPolynomial.twistCoordinates (Y (src e)) ⟨b, r⟩ ∈ K := by
          apply IntermediateField.subset_adjoin
          exact Or.inl (Or.inl ⟨⟨src e, ⟨b, r⟩⟩, rfl⟩)
        have hDst :
            GroundedTwistPolynomial.twistCoordinates (Y (dst e)) ⟨b, r⟩ ∈ K := by
          apply IntermediateField.subset_adjoin
          exact Or.inl (Or.inl ⟨⟨dst e, ⟨b, r⟩⟩, rfl⟩)
        simpa [Z] using K.sub_mem hSrc hDst
      · have hx' : x = p e (chart e') := by simpa using hx
        subst x
        apply IntermediateField.subset_adjoin
        exact Or.inl (Or.inr ⟨e', rfl⟩)
    apply hSmallLe
    exact pinCoordinate_mem_adjoin_of_eval_eq_zero
      Z (p e) (chart e') j (hchart e') (hY.2 e')
  · apply IntermediateField.subset_adjoin
    exact Or.inr ⟨⟨⟨e, he⟩, j⟩, rfl⟩

/-- An occurrence selected by `active` determines a genuine simple edge.
The membership proof is retained so that the non-loop hypothesis is applied
to the exact occurrence used by the incidence equation. -/
def activeEdge {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) : SimpleEdge V :=
  ⟨s(src e.1, dst e.1), by
    rw [Sym2.mk_isDiag_iff]
    exact hLoop e.1 e.2⟩

/--
For any finite provenance-labelled occurrence system, a sparse null
skeleton of the exact dimension-budget cardinality forces the image of the
distinct incidence locus to lie in a proper integer hypersurface of the pin
coordinate space.  Inactive occurrences are deliberately retained in the
ambient polynomial ring; the resulting polynomial may ignore them, but its
nonvanishing is asserted in the full provenance-labelled ring.

This proposition contains no body--pin graph, partition, or rigidity
predicate.
-/
def PropernessPrinciple : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E]
      (src dst : E → V) (active : Finset E)
      (hLoop : ∀ e ∈ active, src e ≠ dst e)
      (F : SimpleEdgeSet V),
    2 ≤ Fintype.card V →
    Sparse22 F →
    (∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) →
    F.card = 6 * (Fintype.card V - 1) - 2 * active.card →
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        IsIncidenceRealization src dst active p Y →
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0

end

end SparseNullIncidence

namespace BodyPinIncidence

noncomputable section

/-- Canonical finite labels for the blocks of an ordinary finpartition. -/
def equalityPartitionFinLabel (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) : H.Body → Fin P.parts.card :=
  P.parts.equivFin ∘ finpartitionBlock P

theorem equalityPartitionFinLabel_surjective (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) :
    Function.Surjective (H.equalityPartitionFinLabel P) := by
  exact P.parts.equivFin.surjective.comp (finpartitionBlock_surjective P)

/-- Actual pin occurrences whose endpoints lie in different exact blocks. -/
def crossingPinsAt (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) : Finset H.Pin :=
  Finset.univ.filter fun e ↦
    H.equalityPartitionFinLabel P (H.left e) ≠
      H.equalityPartitionFinLabel P (H.right e)

@[simp]
theorem mem_crossingPinsAt (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) (e : H.Pin) :
    e ∈ H.crossingPinsAt P ↔
      H.equalityPartitionFinLabel P (H.left e) ≠
        H.equalityPartitionFinLabel P (H.right e) := by
  simp [crossingPinsAt]

/-- The fixed equality partition is in the small-bundle branch.  This is the
literal occurrence multiplicity condition on its canonical finite labels. -/
def HasOnlySmallBundlesAt (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) : Prop :=
  ∀ e ∈ H.fineSupportOn (H.equalityPartitionFinLabel P),
    H.fineMultiplicityOn (H.equalityPartitionFinLabel P) e ≤ 2

/-- The small/triple dichotomy is exhaustive at the occurrence level.  If a
fine crossing bundle is not small, its filtered occurrence fibre contains
three pairwise distinct pins, which retain enough provenance to build the
already verified triple-bundle certificate. -/
theorem hasOnlySmallBundlesAt_or_tripleBundlePartitionCertificate
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex) :
    H.HasOnlySmallBundlesAt P ∨
      Nonempty (H.TripleBundlePartitionCertificate P) := by
  classical
  by_cases hSmall : H.HasOnlySmallBundlesAt P
  · exact Or.inl hSmall
  · right
    simp only [HasOnlySmallBundlesAt] at hSmall
    push Not at hSmall
    obtain ⟨f, hf, hlarge⟩ := hSmall
    rcases f with ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ i j =>
        let π := H.equalityPartitionFinLabel P
        let T : Finset H.Pin := Finset.univ.filter fun e ↦
          s(π (H.left e), π (H.right e)) = s(i, j)
        have hTcard : 3 ≤ T.card := by
          have hlarge' : ¬
              H.fineMultiplicityOn π ⟨s(i, j), hz⟩ ≤ 2 := by
            simpa [π] using hlarge
          have hThree : 3 ≤
              H.fineMultiplicityOn π
                ⟨s(i, j), hz⟩ := by
            omega
          simpa [T, BodyPinIncidence.fineMultiplicityOn,
            BodyPinIncidence.bundleMultiplicityOn] using hThree
        obtain ⟨e₀, e₁, e₂, he₀, he₁, he₂, h₀₁, h₀₂, h₁₂⟩ :=
          Finset.two_lt_card_iff.mp (by omega : 2 < T.card)
        have hpair₀ :
            s(π (H.left e₀), π (H.right e₀)) = s(i, j) := by
          simpa [T] using he₀
        have hpair₁ :
            s(π (H.left e₁), π (H.right e₁)) = s(i, j) := by
          simpa [T] using he₁
        have hpair₂ :
            s(π (H.left e₂), π (H.right e₂)) = s(i, j) := by
          simpa [T] using he₂
        let A : P.parts := P.parts.equivFin.symm i
        let B : P.parts := P.parts.equivFin.symm j
        have hij : i ≠ j := by
          simpa [Sym2.mk_isDiag_iff] using hz
        have hAB : A ≠ B := by
          intro hEq
          apply hij
          have := congrArg P.parts.equivFin hEq
          simpa [A, B] using this
        have joins_of_pair (e : H.Pin)
            (hpair : s(π (H.left e), π (H.right e)) = s(i, j)) :
            H.PinJoinsBlocks P A B e := by
          rw [Sym2.eq_iff] at hpair
          rcases hpair with hForward | hReverse
          · left
            constructor
            · apply P.parts.equivFin.injective
              simpa [A, π, equalityPartitionFinLabel] using hForward.1
            · apply P.parts.equivFin.injective
              simpa [B, π, equalityPartitionFinLabel] using hForward.2
          · right
            constructor
            · apply P.parts.equivFin.injective
              simpa [B, π, equalityPartitionFinLabel] using hReverse.1
            · apply P.parts.equivFin.injective
              simpa [A, π, equalityPartitionFinLabel] using hReverse.2
        exact ⟨
          { first := e₀
            second := e₁
            third := e₂
            first_ne_second := h₀₁
            first_ne_third := h₀₂
            second_ne_third := h₁₂
            blockA := A
            blockB := B
            blocks_ne := hAB
            first_joins := joins_of_pair e₀ hpair₀
            second_joins := joins_of_pair e₁ hpair₁
            third_joins := joins_of_pair e₂ hpair₂ }⟩

/-- Fine mass is exactly the number of provenance-labelled pin occurrences
which cross the labelled partition. -/
theorem card_crossingPinsAt_eq_fineMassOn
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex) :
    (H.crossingPinsAt P).card =
      H.fineMassOn (H.equalityPartitionFinLabel P) := by
  classical
  let π := H.equalityPartitionFinLabel P
  let pair : H.Pin → Sym2 (Fin P.parts.card) :=
    fun e ↦ s(π (H.left e), π (H.right e))
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset H.Pin)
    ((⊤ : SimpleGraph (Fin P.parts.card)).edgeFinset) pair
  calc
    (H.crossingPinsAt P).card =
        (Finset.univ.filter fun e : H.Pin ↦
          pair e ∈ (⊤ : SimpleGraph (Fin P.parts.card)).edgeFinset).card := by
      congr 1
      ext e
      simp only [crossingPinsAt, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
      change (π (H.left e) ≠ π (H.right e)) ↔ ¬ (pair e).IsDiag
      simp [pair, Sym2.mk_isDiag_iff]
    _ = ∑ b ∈ (⊤ : SimpleGraph (Fin P.parts.card)).edgeFinset,
          H.bundleMultiplicityOn π b := by
      rw [← hFiber]
      apply Finset.sum_congr rfl
      intro b hb
      unfold BodyPinIncidence.bundleMultiplicityOn
      congr 1
    _ = ∑ e : SimpleEdge (Fin P.parts.card),
          H.fineMultiplicityOn π e := by
      exact sum_completeEdges_eq_sum_simpleEdges
        (fun b ↦ H.bundleMultiplicityOn π b)
    _ = H.fineMassOn π := by
      exact (H.fineMassOn_eq_sum_simpleEdges π).symm

/-- A selected crossing occurrence really has distinct finite block labels. -/
theorem crossingPinsAt_loopless (H : BodyPinIncidence)
    (P : H.EqualityPartitionIndex) :
    ∀ e ∈ H.crossingPinsAt P,
      H.equalityPartitionFinLabel P (H.left e) ≠
        H.equalityPartitionFinLabel P (H.right e) := by
  intro e he
  exact (H.mem_crossingPinsAt P e).mp he

/-- Every edge of the fine support is represented by an actual crossing pin
occurrence.  This is the provenance bridge used by the null-incidence
properness principle. -/
theorem exists_crossingPin_activeEdge_eq
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex)
    (f : SimpleEdge (Fin P.parts.card))
    (hf : f ∈ H.fineSupportOn (H.equalityPartitionFinLabel P)) :
    ∃ e : H.crossingPinsAt P,
      SparseNullIncidence.activeEdge
        (H.equalityPartitionFinLabel P ∘ H.left)
        (H.equalityPartitionFinLabel P ∘ H.right)
        (H.crossingPinsAt P) (H.crossingPinsAt_loopless P) e = f := by
  classical
  let π := H.equalityPartitionFinLabel P
  have hpos : 0 < H.fineMultiplicityOn π f :=
    (H.mem_fineSupportOn π f).mp hf
  have hnonempty :
      (Finset.univ.filter fun e : H.Pin ↦
        s(π (H.left e), π (H.right e)) = f.1).Nonempty := by
    rw [← Finset.card_pos]
    exact hpos
  obtain ⟨e, he⟩ := hnonempty
  have hpair : s(π (H.left e), π (H.right e)) = f.1 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  have hcross : e ∈ H.crossingPinsAt P := by
    apply (H.mem_crossingPinsAt P e).mpr
    intro heq
    apply f.2
    rw [← hpair]
    simpa [Sym2.mk_isDiag_iff] using heq
  refine ⟨⟨e, hcross⟩, ?_⟩
  apply Subtype.ext
  exact hpair

/-- A non-diagonal twist assignment has at least two exact equality blocks. -/
theorem two_le_card_equalityPartition_parts
    {W : Type*} [Fintype W] [DecidableEq W]
    (X : W → Twist ℝ) (hX : ¬ IsDiagonalTwist X) :
    2 ≤ (equalityPartition X).parts.card := by
  by_contra hnot
  have hcard : (equalityPartition X).parts.card ≤ 1 := by omega
  apply hX
  cases isEmpty_or_nonempty W with
  | inl hEmpty =>
      letI : IsEmpty W := hEmpty
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
  | inr hNonempty =>
      letI : Nonempty W := hNonempty
      let w₀ : W := Classical.choice hNonempty
      refine ⟨X w₀, funext fun w ↦ ?_⟩
      apply (equalityPartition_part_eq_iff X w w₀).mp
      apply Finset.card_le_one.mp hcard
      · exact (equalityPartition X).part_mem.mpr (by simp)
      · exact (equalityPartition X).part_mem.mpr (by simp)

/-- Exact block values, reindexed by the canonical finite block labels. -/
def finiteEqualityBlockValue
    {W : Type*} [Fintype W] [DecidableEq W]
    (X : W → Twist ℝ) :
    Fin (equalityPartition X).parts.card → Twist ℝ :=
  equalityBlockValue X ∘ (equalityPartition X).parts.equivFin.symm

theorem finiteEqualityBlockValue_injective
    {W : Type*} [Fintype W] [DecidableEq W]
    (X : W → Twist ℝ) :
    Function.Injective (finiteEqualityBlockValue X) :=
  (equalityBlockValue_injective X).comp
    (equalityPartition X).parts.equivFin.symm.injective

@[simp]
theorem finiteEqualityBlockValue_finLabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (X : W → Twist ℝ) (w : W) :
    finiteEqualityBlockValue X
        ((equalityPartition X).parts.equivFin
          (finpartitionBlock (equalityPartition X) w)) = X w := by
  simp [finiteEqualityBlockValue]

/-- The canonical injective block-value configuration of any twist motion is
an incidence realization on precisely the crossing occurrences of its exact
equality partition. -/
theorem finiteEqualityBlockValue_isIncidenceRealization
    (H : BodyPinIncidence) (p : H.Pin → Vec3 ℝ)
    (X : H.Body → Twist ℝ)
    (hMotion : IsTwistMotion H.left H.right p X) :
    SparseNullIncidence.IsIncidenceRealization
      (H.equalityPartitionFinLabel (equalityPartition X) ∘ H.left)
      (H.equalityPartitionFinLabel (equalityPartition X) ∘ H.right)
      (H.crossingPinsAt (equalityPartition X)) p
      (finiteEqualityBlockValue X) := by
  refine ⟨finiteEqualityBlockValue_injective X, ?_⟩
  intro e
  simpa [equalityPartitionFinLabel] using
    (eval_sub_eq_zero_of_isTwistMotion hMotion e.1)

/--
For one fixed small-bundle equality partition, the universal sparse
null-incidence properness principle constructs the exact nonzero integer
polynomial required by `FiniteBadCover`.

The empty-stratum case uses the constant polynomial `1`.  In the nonempty
case, non-diagonality supplies at least two blocks, and all other hypotheses
of the properness principle are proved from the partition condition and the
literal occurrence data.
-/
theorem exists_smallBundlePartitionPolynomial
    (H : BodyPinIncidence) (P : H.EqualityPartitionIndex)
    (hPartition : H.PartitionCondition)
    (hSmall : H.HasOnlySmallBundlesAt P)
    (hProper : SparseNullIncidence.PropernessPrinciple) :
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ,
      Q ≠ 0 ∧
      ∀ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
        H.ExactBadMotionAt P p X →
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
  classical
  by_cases hBad : ∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
      H.ExactBadMotionAt P p X
  · obtain ⟨p₀, X₀, hBad₀⟩ := hBad
    have ht : 2 ≤ P.parts.card := by
      have ht₀ := two_le_card_equalityPartition_parts X₀ hBad₀.2.2
      simpa [hBad₀.2.1] using ht₀
    let π := H.equalityPartitionFinLabel P
    obtain ⟨F, hFsupport, hFsparse, hFcard⟩ :=
      H.exists_sparse_nullSkeleton π
        (H.equalityPartitionFinLabel_surjective P) ht hPartition hSmall
    have hLoop := H.crossingPinsAt_loopless P
    obtain ⟨Q, hQ, hQvanish⟩ := hProper
      (Fin P.parts.card) H.Pin
      (π ∘ H.left) (π ∘ H.right) (H.crossingPinsAt P)
      hLoop F (by simpa using ht) hFsparse
      (by
        intro f hf
        exact H.exists_crossingPin_activeEdge_eq P f (hFsupport hf))
      (by
        rw [hFcard, H.card_crossingPinsAt_eq_fineMassOn P]
        simp [BodyPinIncidence.sparseSkeletonTarget, π])
    refine ⟨Q, hQ, ?_⟩
    intro p X hExact
    rcases hExact with ⟨hMotion, hEquality, hNonDiagonal⟩
    subst P
    apply hQvanish p (finiteEqualityBlockValue X)
    simpa [π] using
      H.finiteEqualityBlockValue_isIncidenceRealization p X hMotion
  · refine ⟨1, one_ne_zero, ?_⟩
    intro p X hExact
    exact (hBad ⟨p, X, hExact⟩).elim

/-- If every bad equality stratum is in the small-bundle branch, the one
universal properness theorem already yields an actual rigid real twist
realization. -/
theorem exists_real_twistRigidAt_of_smallBundleProperness
    (H : BodyPinIncidence) (hPartition : H.PartitionCondition)
    (hProper : SparseNullIncidence.PropernessPrinciple)
    (hSmall : ∀ (P : H.EqualityPartitionIndex),
      (∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
    H.ExactBadMotionAt P p X) → H.HasOnlySmallBundlesAt P) :
    HasRigidTwistRealization (k := ℝ) H.left H.right := by
  classical
  have hCertificate : ∀ P : H.EqualityPartitionIndex,
      ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ,
        Q ≠ 0 ∧
        ∀ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
          H.ExactBadMotionAt P p X →
          MvPolynomial.eval₂ (Int.castRingHom ℝ)
            (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
    intro P
    by_cases hBad : ∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
        H.ExactBadMotionAt P p X
    · exact H.exists_smallBundlePartitionPolynomial P hPartition
        (hSmall P hBad) hProper
    · refine ⟨1, one_ne_zero, ?_⟩
      intro p X hExact
      exact (hBad ⟨p, X, hExact⟩).elim
  choose Q hQ hQvanish using hCertificate
  exact H.exists_real_twistRigidAt_of_partitionCertificates Q hQ hQvanish

/-- The same conditional small-bundle packet reaches the literal expanded
bar--joint generic-rigidity semantics. -/
theorem genericallyRigidInR3_of_smallBundleProperness
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (hPartition : H.PartitionCondition)
    (hProper : SparseNullIncidence.PropernessPrinciple)
    (hSmall : ∀ (P : H.EqualityPartitionIndex),
      (∃ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
        H.ExactBadMotionAt P p X) → H.HasOnlySmallBundlesAt P) :
    H.GenericallyRigidInR3 extra := by
  apply H.genericallyRigidInR3_of_hasRigidTwistRealization extra
  exact H.exists_real_twistRigidAt_of_smallBundleProperness
    hPartition hProper hSmall

/-- The occurrence-level small/triple dichotomy removes the last
partition-classification hypothesis: triple bundles use their explicit minor,
and all remaining partitions use the sparse null-incidence properness
principle.  Thus the entire twist sufficiency direction is conditional on
one body--pin-independent universal proposition. -/
theorem exists_real_twistRigidAt_of_sparseNullIncidenceProperness
    (H : BodyPinIncidence) (hPartition : H.PartitionCondition)
    (hProper : SparseNullIncidence.PropernessPrinciple) :
    HasRigidTwistRealization (k := ℝ) H.left H.right := by
  classical
  have hCertificate : ∀ P : H.EqualityPartitionIndex,
      ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable H.Pin) ℤ,
        Q ≠ 0 ∧
        ∀ (p : H.Pin → Vec3 ℝ) (X : H.Body → Twist ℝ),
          H.ExactBadMotionAt P p X →
          MvPolynomial.eval₂ (Int.castRingHom ℝ)
            (GroundedTwistPolynomial.assignmentOfPins p) Q = 0 := by
    intro P
    rcases H.hasOnlySmallBundlesAt_or_tripleBundlePartitionCertificate P with
      hSmall | hTriple
    · exact H.exists_smallBundlePartitionPolynomial P hPartition hSmall hProper
    · rcases hTriple with ⟨C⟩
      exact ⟨C.polynomial, C.polynomial_ne_zero,
        C.polynomial_eq_zero_of_exactBadMotionAt⟩
  choose Q hQ hQvanish using hCertificate
  exact H.exists_real_twistRigidAt_of_partitionCertificates Q hQ hQvanish

/-- Conditional sufficiency for the literal expanded three-dimensional
bar--joint graph.  No restricted graph class or surrogate rigidity notion
appears in the conclusion. -/
theorem genericallyRigidInR3_of_sparseNullIncidenceProperness
    (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (hPartition : H.PartitionCondition)
    (hProper : SparseNullIncidence.PropernessPrinciple) :
    H.GenericallyRigidInR3 extra := by
  apply H.genericallyRigidInR3_of_hasRigidTwistRealization extra
  exact H.exists_real_twistRigidAt_of_sparseNullIncidenceProperness
    hPartition hProper

end

end BodyPinIncidence

/-- The universal sparse-null incidence properness proposition, together
with necessity, implies the body--pin equivalence. -/
theorem endToEndBodyPinStatement_of_sparseNullIncidenceProperness
    (hProper : SparseNullIncidence.PropernessPrinciple) :
    EndToEndBodyPinStatement := by
  rw [endToEndBodyPinStatement_iff_sufficiency]
  intro H extra hPartition
  exact H.genericallyRigidInR3_of_sparseNullIncidenceProperness
    extra hPartition hProper

end RB31E2E
