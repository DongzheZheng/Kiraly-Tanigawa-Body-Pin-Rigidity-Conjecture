import RB31EndToEnd.NullCellule.GroundedPFEndToEnd
import RB31EndToEnd.NullCellule.ProvenanceFlagBranch
import RB31EndToEnd.Combinatorics.Sparse22.Transport
import RB31EndToEnd.Linear.DirectionStressBaseChange
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-!
# From provenance-flag semismallness to grounded PF

The provenance-flag theorem is naturally ungrounded: its empty-flag
specialization has ambient dimension `3 * |V|`.  The selected-null height
assembly needs the corresponding root-zero estimate with ambient dimension
`3 * (|V| - 1)`.

This file proves the exact bridge.  Starting with a root-zero placement over
`K`, it adjoins three independent common-translation variables.  Common
translation leaves every direction row, hence the stress space, unchanged,
while the function-field transcendence degree increases by exactly three.
Applying empty-flag semismallness upstairs and cancelling those three
dimensions gives the grounded estimate.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlagGroundedPF

open ProvenanceFlag

/-! ## Three independent common translations -/

abbrev TranslationRing (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

abbrev TranslationField (K : Type*) [Field K] :=
  FractionRing (TranslationRing K)

def translationCoordinate {K : Type*} [Field K] (j : Fin 3) :
    TranslationField K :=
  algebraMap (TranslationRing K) (TranslationField K) (MvPolynomial.X j)

def translatedPlacement
    {K V : Type*} [Field K]
    (a : V → Fin 3 → K) : V → Fin 3 → TranslationField K :=
  fun v j ↦ algebraMap K (TranslationField K) (a v j) +
    translationCoordinate j

theorem translatedPlacement_root
    {K V : Type*} [Field K] {a : V → Fin 3 → K} {root : V}
    (hroot : a root = 0) (j : Fin 3) :
    translatedPlacement a root j = translationCoordinate j := by
  simp [translatedPlacement, hroot]

theorem translatedPlacement_injective
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (ha : Function.Injective a) :
    Function.Injective (translatedPlacement a) := by
  intro u v huv
  apply ha
  funext j
  have hj := congrFun huv j
  simp only [translatedPlacement] at hj
  have : algebraMap K (TranslationField K) (a u j) =
      algebraMap K (TranslationField K) (a v j) := by
    exact add_right_cancel hj
  exact (RingHom.injective (algebraMap K (TranslationField K))) this

theorem directionRow_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (e : SimpleEdge V) :
    DirectionStress.directionRow (translatedPlacement a) e =
      DirectionStress.directionRow
        (DirectionStress.mapPlacement (K := TranslationField K) a) e := by
  funext v j
  simp only [DirectionStress.directionRow, DirectionStress.edgeDirection,
    translatedPlacement, DirectionStress.mapPlacement]
  split_ifs <;> ring

theorem directionStressDim_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) :
    DirectionStress.directionStressDim F (translatedPlacement a) =
      DirectionStress.directionStressDim F a := by
  have hmap :
      DirectionStress.directionEquilibrium F (translatedPlacement a) =
        DirectionStress.directionEquilibrium F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
    apply LinearMap.ext
    intro weight
    funext v j
    simp only [DirectionStress.directionEquilibrium_apply,
      DirectionStress.directionEquilibriumCoordinate]
    apply Finset.sum_congr rfl
    intro e _he
    rw [directionRow_translatedPlacement a e.1]
  calc
    DirectionStress.directionStressDim F (translatedPlacement a) =
        DirectionStress.directionStressDim F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
      unfold DirectionStress.directionStressDim
      change Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F (translatedPlacement a))) =
        Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F
              (DirectionStress.mapPlacement
                (K := TranslationField K) a)))
      rw [hmap]
    _ = DirectionStress.directionStressDim F a :=
      DirectionStress.directionStressDim_mapPlacement F a

/-! ## The translation field has relative transcendence degree three -/

theorem adjoin_translationCoordinate_eq_top
    {K : Type*} [Field K] :
    IntermediateField.adjoin K (Set.range (translationCoordinate (K := K))) =
      ⊤ := by
  let A : IntermediateField K (TranslationField K) :=
    IntermediateField.adjoin K
      (Set.range (translationCoordinate (K := K)))
  have hX (j : Fin 3) : translationCoordinate (K := K) j ∈ A :=
    IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [A, IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using
          A.algebraMap_mem c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using A.mul_mem hp (hX j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

theorem translationCoordinate_isTranscendenceBasis
    {K : Type*} [Field K] :
    IsTranscendenceBasis K (translationCoordinate (K := K)) := by
  let R := TranslationRing K
  let L := TranslationField K
  have hInjective : Function.Injective
      (algebraMap R L) := IsFractionRing.injective R L
  have hIndependent : AlgebraicIndependent K
      (translationCoordinate (K := K)) := by
    have hX := MvPolynomial.algebraicIndependent_X (Fin 3) K
    have hmap := hX.map
      (f := IsScalarTower.toAlgHom K R L)
      hInjective.injOn
    simpa [R, L, translationCoordinate, Function.comp_def] using hmap
  have hField : Algebra.IsAlgebraic
      (IntermediateField.adjoin K
        (Set.range (translationCoordinate (K := K)))) L :=
    ⟨fun z ↦ by
      have hz : z ∈ IntermediateField.adjoin K
          (Set.range (translationCoordinate (K := K))) := by
        rw [adjoin_translationCoordinate_eq_top]
        exact trivial
      have hmap : algebraMap
          (IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) L
          (⟨z, hz⟩ : IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) = z := rfl
      rw [← hmap]
      exact isAlgebraic_algebraMap _⟩
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hIndependent, ?_⟩
  exact (IntermediateField.isAlgebraic_adjoin_iff_top).mp hField

theorem trdeg_translationField
    {K : Type*} [Field K] :
    Algebra.trdeg K (TranslationField K) = 3 := by
  simpa using
    (translationCoordinate_isTranscendenceBasis
      (K := K)).lift_cardinalMk_eq_trdeg.symm

theorem trdeg_translationField_over_base
    {k K : Type*} [Field k] [Field K] [Algebra k K] :
    Algebra.trdeg k (TranslationField K) = Algebra.trdeg k K + 3 := by
  calc
    Algebra.trdeg k (TranslationField K) =
        Algebra.trdeg k K + Algebra.trdeg K (TranslationField K) :=
      (trdeg_add_eq k K).symm
    _ = Algebra.trdeg k K + 3 := by rw [trdeg_translationField]

/-! ## The translated placement still generates the whole field -/

theorem translatedPlacement_generated
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (root : V)
    (hroot : a root = 0)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤) :
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2)) = ⊤ := by
  let A : IntermediateField k (TranslationField K) :=
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2))
  have htranslated (v : V) (j : Fin 3) :
      translatedPlacement a v j ∈ A :=
    IntermediateField.subset_adjoin k _ ⟨⟨v, j⟩, rfl⟩
  have htranslation (j : Fin 3) :
      translationCoordinate (K := K) j ∈ A := by
    rw [← translatedPlacement_root hroot j]
    exact htranslated root j
  have hcoordinate (v : V) (j : Fin 3) :
      algebraMap K (TranslationField K) (a v j) ∈ A := by
    have hsub := A.sub_mem (htranslated v j) (htranslation j)
    simpa [translatedPlacement] using hsub
  have hbase (x : K) : algebraMap K (TranslationField K) x ∈ A := by
    have hx : x ∈ IntermediateField.adjoin k
        (Set.range (fun y : V × Fin 3 ↦ a y.1 y.2)) := by
      rw [hgen]
      exact trivial
    exact IntermediateField.adjoin_induction k
      (p := fun y _hy ↦ algebraMap K (TranslationField K) y ∈ A)
      (fun y hy ↦ by
        obtain ⟨⟨v, j⟩, rfl⟩ := hy
        exact hcoordinate v j)
      (fun c ↦ by
        simpa [IsScalarTower.algebraMap_apply k K (TranslationField K)] using
          A.algebraMap_mem c)
      (fun _ _ _ _ hy hz ↦ by simpa using A.add_mem hy hz)
      (fun _ _ hy ↦ by simpa using A.inv_mem hy)
      (fun _ _ _ _ hy hz ↦ by simpa using A.mul_mem hy hz)
      hx
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using hbase c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using
          A.mul_mem hp (htranslation j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

/-! ## Empty flags and completion sparsity -/

def emptyFlagState {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) : ProvenanceFlag.State V (Fin 0) where
  edges := F
  terminals := Fin.elim0
  missing := Fin.elim0
  terminals_card := fun t ↦ Fin.elim0 t
  missing_supported := fun t ↦ Fin.elim0 t
  missing_not_live := fun t ↦ Fin.elim0 t
  other_terminal_edges_live := fun t ↦ Fin.elim0 t

theorem emptyFlagState_completionEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) :
    (emptyFlagState F).completionEdges =
      (emptyFlagState F).liftedLiveEdges := by
  simp [ProvenanceFlag.State.completionEdges,
    ProvenanceFlag.State.restoredMissingEdges,
    ProvenanceFlag.State.ghostStarEdges]

theorem map_drop_liftLiveEdge
    {V : Type*} [DecidableEq V] (e : SimpleEdge V) :
    Sparse22Transport.mapSimpleEdge
        (Equiv.sumEmpty V (Fin 0)).toEmbedding
        (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) e) = e := by
  apply Subtype.ext
  simp [Sparse22Transport.mapSimpleEdge,
    ProvenanceFlag.liftLiveEdge, Sym2.map_map]

theorem emptyFlagState_completionSparse
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (hF : Sparse22 F) :
    (emptyFlagState F).CompletionSparse := by
  rw [ProvenanceFlag.State.CompletionSparse,
    emptyFlagState_completionEdges]
  apply Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (Equiv.sumEmpty V (Fin 0)).toEmbedding hF
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hg
  change Sparse22Transport.mapSimpleEdge
      (Equiv.sumEmpty V (Fin 0)).toEmbedding
      (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) f) ∈ F
  rw [map_drop_liftLiveEdge]
  exact hf

/-! ## Passage to the grounded inequality -/

/-- Empty-flag semismallness implies the rooted direction-stress inequality.
Grounding and all cardinal conversions are proved in this declaration. -/
theorem groundedPF_of_provenanceFlag_semismallness
    (hFlagPF :
      ∀ {k K V Flag : Type}
        [Field k] [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V]
        [Fintype Flag] [DecidableEq Flag]
        (S : ProvenanceFlag.State V Flag),
        S.CompletionSparse →
        ∀ Y : ProvenanceFlag.FunctionFieldBranch (k := k) (K := K) S,
          Y.SemismallBudget S) :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (F : SimpleEdgeSet V), Sparse22 F →
      ∀ (root : V) {K : Type} [Field K] [Algebra ℚ K]
        (a : V → Fin 3 → K),
        a root = 0 →
        Function.Injective a →
        IntermediateField.adjoin ℚ
            (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
        DirectionStress.directionStressDim F a +
            (Algebra.trdeg ℚ K).toNat ≤
          Nat.card (GroundedTwistSplit.SpatialVariable root) := by
  intro V _instFV _instDV F hSparse root K _instFieldK _instAlgQK
    a hroot hinjective hgenerated
  let S := emptyFlagState F
  let Y : ProvenanceFlag.FunctionFieldBranch
      (k := ℚ) (K := TranslationField K) S := {
    position := translatedPlacement a
    generated := translatedPlacement_generated a root hroot hgenerated
    distinct := translatedPlacement_injective a hinjective
    collinear := fun t ↦ Fin.elim0 t
  }
  have hBudget := hFlagPF S (emptyFlagState_completionSparse F hSparse) Y
  have hEmptyBudget :
      (Y.stressDim S : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) :=
    (Y.semismallBudget_of_flag_card_zero_iff S (by simp)).mp hBudget
  change
      (DirectionStress.directionStressDim F (translatedPlacement a) : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) at hEmptyBudget
  rw [directionStressDim_translatedPlacement,
    trdeg_translationField_over_base] at hEmptyBudget
  have hTrdegFinite : Algebra.trdeg ℚ K < Cardinal.aleph0 :=
    (FiniteCoordinateTrdeg.trdeg_le_three_mul_card
      (fun x : V × Fin 3 ↦ a x.1 x.2) hgenerated).trans_lt
        (Cardinal.mul_lt_aleph0
          Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0)
  have hRightFinite :
      3 * (Fintype.card V : Cardinal) < Cardinal.aleph0 :=
    Cardinal.mul_lt_aleph0
      Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0
  have hNat := Cardinal.toNat_le_toNat hEmptyBudget hRightFinite
  have hStressFinite :
      (DirectionStress.directionStressDim F a : Cardinal) <
        Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have hThreeFinite : (3 : Cardinal) < Cardinal.aleph0 := by simp
  rw [Cardinal.toNat_add hStressFinite
      (Cardinal.add_lt_aleph0 hTrdegFinite hThreeFinite),
    Cardinal.toNat_add hTrdegFinite hThreeFinite] at hNat
  simp at hNat
  have hOffRoot :
      Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V ↦ v = root)]
    simp
  rw [Nat.card_eq_fintype_card]
  simp only [GroundedTwistSplit.SpatialVariable,
    Fintype.card_prod, Fintype.card_fin, hOffRoot]
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

/-- The all-flags semismallness theorem implies the body--pin statement. -/
theorem endToEndBodyPinStatement_of_provenanceFlag_semismallness
    (hFlagPF :
      ∀ {k K V Flag : Type}
        [Field k] [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V]
        [Fintype Flag] [DecidableEq Flag]
        (S : ProvenanceFlag.State V Flag),
        S.CompletionSparse →
        ∀ Y : ProvenanceFlag.FunctionFieldBranch (k := k) (K := K) S,
          Y.SemismallBudget S) :
    EndToEndBodyPinStatement :=
  endToEndBodyPinStatement_of_groundedPF
    (groundedPF_of_provenanceFlag_semismallness hFlagPF)

end ProvenanceFlagGroundedPF

end

end RB31E2E
