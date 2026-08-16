import RB31EndToEnd.Linear.OutsideLocalPayment

/-!
# The linear core of the outside local classification

For a vertex `v`, let `C_v` be the literal local equilibrium map on the
incident-edge packet.  This file proves the part of the outside-local lemma
which is pure finite-dimensional linear algebra:

* the response kernel is a subspace of `ker C_v`;
* rank--nullity for `C_v` is exactly the degree ledger;
* an injective placement makes `C_v` have positive rank whenever `v` has an
  incident edge;
* under degree at most three, failure of the three-coordinate payment has
  only two numerical shapes;
* if `rank C_v >= 2`, the only shape is
  `degree = 3`, extension cost `= 3`, response dimension `= 1`, and
  `dim ker C_v = 1`.

The retained-neighbour geometry then rules out the rank-one numerical
branch.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-- Nullity of the literal local equilibrium map `C_v`. -/
def outsideLocalKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : ℕ :=
  Module.finrank K (LinearMap.ker (localEquilibriumAt F a v))

/-- Rank of the literal local equilibrium map `C_v`. -/
def outsideLocalRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) : ℕ :=
  Module.finrank K (LinearMap.range (localEquilibriumAt F a v))

/-- The response kernel is literally a submodule of `ker C_v`. -/
theorem outsideResponseKernelDim_le_outsideLocalKernelDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    outsideResponseKernelDim F a v ≤ outsideLocalKernelDim F a v := by
  simpa [outsideResponseKernelDim, outsideLocalKernelDim] using
    (LinearMap.ker (deletedConnectingClass F a v)).finrank_le

/-- Rank--nullity for `C_v`, with its domain cardinality identified with
the graph-theoretic degree of `v`. -/
theorem outsideLocalRank_add_kernelDim_eq_degree
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    outsideLocalRank F a v + outsideLocalKernelDim F a v =
      edgeSetDegree F v := by
  have hRankNullity :=
    (localEquilibriumAt F a v).finrank_range_add_finrank_ker
  have hDomain :
      Module.finrank K (incidentEdges F v → K) = edgeSetDegree F v := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    rfl
  simpa [outsideLocalRank, outsideLocalKernelDim, hDomain] using
    hRankNullity

omit [Fintype V] in
/-- A single incident-edge coefficient synthesizes its local direction
column at the deleted vertex. -/
@[simp]
theorem localEquilibriumAt_piSingle
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (e : incidentEdges F v) (c : K) :
    localEquilibriumAt F a v (Pi.single e c) =
      c • directionRow a e.1 v := by
  let weight : incidentEdges F v → K := Pi.single e c
  funext j
  change
    (∑ x ∈ (incidentEdges F v).attach,
      weight x * directionRow a x.1 v j) =
        c * directionRow a e.1 v j
  rw [Finset.sum_eq_single e]
  · simp [weight]
  · intro b _ hbe
    simp [weight, hbe]
  · intro he
    exact (he (Finset.mem_attach (incidentEdges F v) e)).elim

omit [Fintype V] [DecidableEq V] in
/-- Distinct placed endpoints give a nonzero oriented edge direction. -/
theorem edgeDirection_ne_zero_of_injective
    (a : V → Fin 3 → K) (ha : Function.Injective a)
    (e : SimpleEdge V) :
    edgeDirection a e ≠ 0 := by
  intro hzero
  apply e.source_ne_target
  apply ha
  funext j
  have hj := congrFun hzero j
  simpa [edgeDirection, sub_eq_zero] using hj

omit [Fintype V] in
/-- At either endpoint of an edge, the local direction row is nonzero for
an injective placement. -/
theorem directionRow_ne_zero_at_incident_of_injective
    (a : V → Fin 3 → K) (ha : Function.Injective a)
    (e : SimpleEdge V) (v : V) (hv : v ∈ e.vertices) :
    directionRow a e v ≠ 0 := by
  have hvEnds : v = e.source ∨ v = e.target := by
    simpa [SimpleEdge.vertices, ← e.source_target_mk,
      Sym2.toFinset_mk_eq] using hv
  rcases hvEnds with hvSource | hvTarget
  · subst v
    simpa using edgeDirection_ne_zero_of_injective a ha e
  · subst v
    simpa using neg_ne_zero.mpr (edgeDirection_ne_zero_of_injective a ha e)

/-- If `v` has an incident edge, then the local equilibrium map has positive
rank at every injective placement. -/
theorem outsideLocalRank_pos_of_injective_of_degree_pos
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a) (hDegree : 0 < edgeSetDegree F v) :
    0 < outsideLocalRank F a v := by
  have hIncident : (incidentEdges F v).Nonempty := by
    apply Finset.card_pos.mp
    simpa [edgeSetDegree] using hDegree
  obtain ⟨edge, hedge⟩ := hIncident
  let e : incidentEdges F v := ⟨edge, hedge⟩
  have hrow : directionRow a e.1 v ≠ 0 := by
    apply directionRow_ne_zero_at_incident_of_injective a ha
    exact (mem_incidentEdges.mp e.2).2
  have hrowRange :
      directionRow a e.1 v ∈ LinearMap.range (localEquilibriumAt F a v) := by
    refine ⟨Pi.single e 1, ?_⟩
    simpa only [one_smul] using localEquilibriumAt_piSingle F a v e 1
  have hSpan :
      K ∙ directionRow a e.1 v ≤
        LinearMap.range (localEquilibriumAt F a v) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hrowRange
  have hDim : 1 ≤
      Module.finrank K (LinearMap.range (localEquilibriumAt F a v)) := by
    calc
      1 = Module.finrank K (K ∙ directionRow a e.1 v) :=
        (finrank_span_singleton hrow).symm
      _ ≤ Module.finrank K
          (LinearMap.range (localEquilibriumAt F a v)) :=
        Submodule.finrank_mono hSpan
  simpa only [outsideLocalRank] using hDim

/-- Pure numerical classification of a failed outside payment.  The first
branch has maximal coordinate-extension cost.  The only alternative has
extension cost two and a rank-one local equilibrium map on exactly three
incident edges. -/
theorem outsidePaymentFailure_linear_dichotomy
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (d : ℕ) (hd : d ≤ 3)
    (hFailure : 3 < outsideResponseKernelDim F a v + d) :
    (d = 3 ∧ 1 ≤ outsideResponseKernelDim F a v) ∨
      (d = 2 ∧
        outsideResponseKernelDim F a v = 2 ∧
        outsideLocalKernelDim F a v = 2 ∧
        outsideLocalRank F a v = 1 ∧
        edgeSetDegree F v = 3) := by
  have hResponseKernel :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F a v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
  have hResponsePos : 0 < outsideResponseKernelDim F a v := by omega
  have hDegreePos : 0 < edgeSetDegree F v := by omega
  have hRankPos :=
    outsideLocalRank_pos_of_injective_of_degree_pos F a v ha hDegreePos
  by_cases hdThree : d = 3
  · exact Or.inl ⟨hdThree, by omega⟩
  · right
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

/-- Once the local equilibrium rank is at least two, failed payment has the
unique numerical shape needed by the outside-local lemma. -/
theorem outsidePaymentFailure_of_two_le_localRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (hDegree : edgeSetDegree F v ≤ 3)
    (d : ℕ) (hd : d ≤ 3)
    (hRank : 2 ≤ outsideLocalRank F a v)
    (hFailure : 3 < outsideResponseKernelDim F a v + d) :
    d = 3 ∧
      outsideResponseKernelDim F a v = 1 ∧
      outsideLocalKernelDim F a v = 1 ∧
      outsideLocalRank F a v = 2 ∧
      edgeSetDegree F v = 3 := by
  have hResponseKernel :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F a v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- The preceding dichotomy instantiated with the actual coordinate-field
extension.  Thus an actual exceptional outside deletion is already reduced
to the maximal-cost branch or the one explicit rank-one branch. -/
theorem outsideExceptional_linear_dichotomy
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hExceptional : OutsideExceptional (k := k) F a v) :
    ((outsideExtensionTrdeg (k := k) a v).toNat = 3 ∧
      1 ≤ outsideResponseKernelDim F a v) ∨
      ((outsideExtensionTrdeg (k := k) a v).toNat = 2 ∧
        outsideResponseKernelDim F a v = 2 ∧
        outsideLocalKernelDim F a v = 2 ∧
        outsideLocalRank F a v = 1 ∧
        edgeSetDegree F v = 3) := by
  have hTrdegCard := outsideExtensionTrdeg_le_three (k := k) a v hgen
  have hTrdegNat : (outsideExtensionTrdeg (k := k) a v).toNat ≤ 3 := by
    simpa using Cardinal.toNat_le_toNat hTrdegCard
  have hFailure :
      3 < outsideResponseKernelDim F a v +
        (outsideExtensionTrdeg (k := k) a v).toNat := by
    unfold OutsideExceptional OutsideNonexceptional at hExceptional
    omega
  exact outsidePaymentFailure_linear_dichotomy F a v ha hDegree
    (outsideExtensionTrdeg (k := k) a v).toNat hTrdegNat hFailure

end

end DirectionStress

end RB31E2E
