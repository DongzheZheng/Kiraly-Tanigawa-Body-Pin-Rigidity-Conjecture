import RB31EndToEnd.Linear.OutsideLocalGeometry
import RB31EndToEnd.NullCellule.ProvenanceFlagBranch

/-!
# The private-flag local classification

This file proves the one-dimensional analogue of the outside local
classification used at a terminal belonging to one provenance flag.  The
input is the literal pivoted shape: the flag line contains `v,p,q`, the
edge `vp` is live, the edge `vq` is missing, and the live degree of `v` is
at most two.

The exceptional alternative is not a tag stored in a graph or branch.  It
is exactly the failure of the transparent one-coordinate payment

`response-kernel dimension + coordinate-extension trdeg <= 1`.

From the actual local equilibrium map and the actual retained-coordinate
field we prove that failure has one shape only: degree two, a unique second
neighbour `z`, four distinct labels `v,p,q,z` on the same line, extension
trdeg one, local and response kernels both one-dimensional, and zero
connecting class.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

/-! ## The literal one-coordinate payment -/

/-- The response kernel fits in the coordinate budget left by the
one-dimensional flag-line fibre. -/
def PrivateNonexceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) : Prop :=
  outsideResponseKernelDim F pos v +
      (outsideExtensionTrdeg (k := k) pos v).toNat ≤ 1

/-- The private exceptional branch is exactly the negation of the local
payment, not an extra hypothesis carried by the state. -/
def PrivateExceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) : Prop :=
  ¬ PrivateNonexceptional (k := k) F pos v

omit [Fintype V] in
theorem private_nonexceptional_or_exceptional
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V) :
    PrivateNonexceptional (k := k) F pos v ∨
      PrivateExceptional (k := k) F pos v := by
  exact em _

omit [Fintype V] in
/-- Cardinal-valued form of the private one-coordinate payment. -/
theorem private_local_payment
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v : V)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hNonexceptional : PrivateNonexceptional (k := k) F pos v) :
    (outsideResponseKernelDim F pos v : Cardinal) +
        outsideExtensionTrdeg (k := k) pos v ≤ 1 := by
  have hfinite := outsideExtensionTrdeg_lt_aleph0 (k := k) pos v hgen
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hfinite]
  exact_mod_cast hNonexceptional

/-! ## Elementary collinearity conversions -/

omit [Fintype V] [DecidableEq V] in
/-- Cyclically permuting three affinely collinear points preserves the
literal witness predicate. -/
theorem collinear_cycle
    (x y z : Fin 3 → K)
    (h : PinCollinearity.Collinear x y z) :
    PinCollinearity.Collinear y z x := by
  obtain ⟨d, c₁, c₂, h₁, h₂⟩ := h
  refine ⟨d, c₂ - c₁, -c₁, ?_, ?_⟩
  · calc
      z - y = (z - x) - (y - x) := by module
      _ = c₂ • d - c₁ • d := by rw [h₁, h₂]
      _ = (c₂ - c₁) • d := by module
  · calc
      x - y = -(y - x) := by module
      _ = -(c₁ • d) := by rw [h₁]
      _ = (-c₁) • d := by module

omit [Fintype V] [DecidableEq V] in
/-- A point written on the affine line through two endpoints gives the
collinearity orientation needed by the private star. -/
theorem collinear_of_point_eq_line
    (point p q : Fin 3 → K) (s : K)
    (hpoint : point = p + s • (q - p)) :
    PinCollinearity.Collinear point p q := by
  refine ⟨q - p, -s, 1 - s, ?_, ?_⟩
  · rw [hpoint]
    module
  · rw [hpoint]
    module

omit [Fintype V] [DecidableEq V] in
/-- Collinearity supplied by the provenance branch on a finite terminal
set implies the three-point predicate used by the direction calculus. -/
theorem pinCollinear_of_affinelyCollinearOn
    (pos : V → Fin 3 → K) (X : Finset V) (x y z : V)
    (h : ProvenanceFlag.AffinelyCollinearOn pos X)
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    PinCollinearity.Collinear (pos x) (pos y) (pos z) := by
  obtain ⟨origin, direction, hall⟩ := h
  obtain ⟨cₓ, hxEq⟩ := hall x hx
  obtain ⟨cᵧ, hyEq⟩ := hall y hy
  obtain ⟨c_z, hzEq⟩ := hall z hz
  refine ⟨direction, cᵧ - cₓ, c_z - cₓ, ?_, ?_⟩
  · rw [hxEq, hyEq]
    module
  · rw [hxEq, hzEq]
    module

omit [Fintype V] in
/-- The pivoted private flag line makes the deleted point a one-parameter
extension of the retained coordinate field. -/
theorem privateExtensionTrdeg_le_one_of_collinear
    (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤) :
    outsideExtensionTrdeg (k := k) pos v ≤ 1 := by
  have hpqPos : pos p ≠ pos q := by
    intro h
    exact hpq (hpos h)
  have hpqv : PinCollinearity.Collinear (pos p) (pos q) (pos v) :=
    collinear_cycle (pos v) (pos p) (pos q) hcol
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (pos p) (pos q) (pos v) hpqPos).1 hpqv
  have hline : ∃ s : K, pos v = pos p + s • (pos q - pos p) := by
    refine ⟨s, ?_⟩
    funext j
    have hj := congrFun hs j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  exact outsideExtensionTrdeg_le_one_of_line_parameter
    (k := k) pos v p q hvp.symm hvq.symm hgen hline

/-! ## A fixed first neighbour and the actual second neighbour -/

/-- The genuine second neighbour of a degree-two private vertex, with the
first neighbour fixed by the pivoted flag edge. -/
structure PrivateSecondNeighbour
    (F : SimpleEdgeSet V) (v p : V) where
  z : V
  hvz : v ≠ z
  hpz : p ≠ z
  vz_mem : simpleEdge v z hvz ∈ F

omit [Fintype V] in
/-- A named live edge `vp` and degree exactly two produce a unique other
edge with an endpoint `z ≠ v,p`.  This is a derived enumeration fact. -/
theorem exists_privateSecondNeighbour
    (F : SimpleEdgeSet V) (v p : V) (hvp : v ≠ p)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hDegree : edgeSetDegree F v = 2) :
    Nonempty (PrivateSecondNeighbour F v p) := by
  have hIncidentCard : (incidentEdges F v).card = 2 := hDegree
  obtain ⟨e₁, e₂, he₁₂, hIncidentEq⟩ :=
    Finset.card_eq_two.mp hIncidentCard
  have hvpIncident : simpleEdge v p hvp ∈ incidentEdges F v := by
    exact mem_incidentEdges.mpr ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩
  have hvpCases : simpleEdge v p hvp = e₁ ∨ simpleEdge v p hvp = e₂ := by
    rw [hIncidentEq] at hvpIncident
    simpa using hvpIncident
  have he₁Incident : e₁ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₂Incident : e₂ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  rcases hvpCases with hvpEq | hvpEq
  · obtain ⟨z, hvz, he₂Eq⟩ :=
      exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂Incident).2
    have hpz : p ≠ z := by
      intro hpz
      subst z
      apply he₁₂
      calc
        e₁ = simpleEdge v p hvp := hvpEq.symm
        _ = simpleEdge v p hvz := by rfl
        _ = e₂ := he₂Eq.symm
    refine ⟨⟨z, hvz, hpz, ?_⟩⟩
    rw [← he₂Eq]
    exact (mem_incidentEdges.mp he₂Incident).1
  · obtain ⟨z, hvz, he₁Eq⟩ :=
      exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁Incident).2
    have hpz : p ≠ z := by
      intro hpz
      subst z
      apply he₁₂
      calc
        e₁ = simpleEdge v p hvz := he₁Eq
        _ = simpleEdge v p hvp := by rfl
        _ = e₂ := hvpEq
    refine ⟨⟨z, hvz, hpz, ?_⟩⟩
    rw [← he₁Eq]
    exact (mem_incidentEdges.mp he₁Incident).1

/-! ## The literal virtual response row -/

omit [Fintype V] in
@[simp]
theorem directionRow_simpleEdge_at_right
    (pos : V → Fin 3 → K) (x y : V) (hxy : x ≠ y) :
    directionRow pos (simpleEdge x y hxy) y = pos y - pos x := by
  rw [simpleEdge_comm x y hxy]
  exact directionRow_simpleEdge_at_left pos y x hxy.symm

omit [Fintype V] in
theorem directionRow_simpleEdge_at_other
    (pos : V → Fin 3 → K) (x y u : V) (hxy : x ≠ y)
    (hux : u ≠ x) (huy : u ≠ y) :
    directionRow pos (simpleEdge x y hxy) u = 0 := by
  apply directionRow_eq_zero_of_ne
  · intro hsource
    have hmem : u ∈ (simpleEdge x y hxy).vertices := by
      rw [← hsource]
      rw [SimpleEdge.vertices,
        ← (simpleEdge x y hxy).source_target_mk]
      simp [Sym2.toFinset_mk_eq]
    rw [vertices_simpleEdge] at hmem
    simp [hux, huy] at hmem
  · intro htarget
    have hmem : u ∈ (simpleEdge x y hxy).vertices := by
      rw [← htarget]
      rw [SimpleEdge.vertices,
        ← (simpleEdge x y hxy).source_target_mk]
      simp [Sym2.toFinset_mk_eq]
    rw [vertices_simpleEdge] at hmem
    simp [hux, huy] at hmem

omit [Fintype V] in
/-- A singleton edge coefficient synthesizes exactly its scalar direction
row in the full vertex-load space. -/
theorem directionEquilibrium_piSingle
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K)
    (e : F) (c : K) :
    directionEquilibrium F pos (Pi.single e c) =
      c • directionRow pos e.1 := by
  rw [directionEquilibrium_eq_sum_smul_directionRow]
  change (∑ x ∈ F.attach,
    (Pi.single e c : F → K) x • directionRow pos x.1) =
      c • directionRow pos e.1
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hbe
    simp [hbe]
  · intro he
    exact (he (Finset.mem_attach F e)).elim

omit [Fintype V] in
/-- The explicit two-star relation on three collinear points has away-load
equal to a scalar multiple of the virtual endpoint row. -/
theorem privateTwoStarRows_eq_virtualRow
    (pos : V → Fin 3 → K) (v p z : V)
    (hvp : v ≠ p) (hvz : v ≠ z) (hpz : p ≠ z) (s : K)
    (hs : pos v - pos p = s • (pos z - pos p)) :
    (1 - s) • directionRow pos (simpleEdge v p hvp) +
        s • directionRow pos (simpleEdge v z hvz) =
      (s * (1 - s)) • directionRow pos (simpleEdge p z hpz) := by
  funext u j
  by_cases huv : u = v
  · subst u
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos v p hvp) j,
      congrFun (directionRow_simpleEdge_at_left pos v z hvz) j,
      congrFun (directionRow_simpleEdge_at_other pos p z v hpz hvp hvz) j]
    have hj := congrFun hs j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  · by_cases hup : u = p
    · subst u
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos v p hvp) j,
        congrFun (directionRow_simpleEdge_at_other pos v z p hvz hvp.symm hpz) j,
        congrFun (directionRow_simpleEdge_at_left pos p z hpz) j]
      have hj := congrFun hs j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hj ⊢
      linear_combination -(1 - s) * hj
    · by_cases huz : u = z
      · subst u
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos v p z hvp hvz.symm hpz.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos v z hvz) j,
          congrFun (directionRow_simpleEdge_at_right pos p z hpz) j]
        have hj := congrFun hs j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        linear_combination -s * hj
      · simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos v p u hvp huv hup) j,
          congrFun (directionRow_simpleEdge_at_other pos v z u hvz huv huz) j,
          congrFun (directionRow_simpleEdge_at_other pos p z u hpz hup huz) j]
        simp

/-! ## Classification of failed private payment -/

/-- Under the pivoted flag shape, failure of the one-coordinate inequality
forces the stated local dimensions and a zero connecting class. -/
theorem privateExceptional_classification
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ N : PrivateSecondNeighbour F v p,
      q ≠ N.z ∧
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) ∧
      outsideExtensionTrdeg (k := k) pos v = 1 ∧
      outsideResponseKernelDim F pos v = 1 ∧
      outsideLocalKernelDim F pos v = 1 ∧
      outsideLocalRank F pos v = 1 ∧
      edgeSetDegree F v = 2 ∧
      deletedConnectingClass F pos v = 0 := by
  let d : ℕ := (outsideExtensionTrdeg (k := k) pos v).toNat
  have hTrdegLeOne := privateExtensionTrdeg_le_one_of_collinear
    (k := k) pos v p q hvp hvq hpq hpos hcol hgen
  have hd : d ≤ 1 := by
    simpa [d] using Cardinal.toNat_le_toNat hTrdegLeOne
  have hFailure : 1 < outsideResponseKernelDim F pos v + d := by
    unfold PrivateExceptional PrivateNonexceptional at hExceptional
    simpa [d] using (show
      1 < outsideResponseKernelDim F pos v +
        (outsideExtensionTrdeg (k := k) pos v).toNat by omega)
  have hResponseLe :=
    outsideResponseKernelDim_le_outsideLocalKernelDim F pos v
  have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F pos v
  have hDegreePos : 0 < edgeSetDegree F v := by
    apply Finset.card_pos.mpr
    exact ⟨simpleEdge v p hvp,
      mem_incidentEdges.mpr ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩⟩
  have hRankPos :=
    outsideLocalRank_pos_of_injective_of_degree_pos F pos v hpos hDegreePos
  have hDegreeTwo : edgeSetDegree F v = 2 := by omega
  have hResponseOne : outsideResponseKernelDim F pos v = 1 := by omega
  have hKernelOne : outsideLocalKernelDim F pos v = 1 := by omega
  have hRankOne : outsideLocalRank F pos v = 1 := by omega
  have hdOne : d = 1 := by omega
  let N : PrivateSecondNeighbour F v p :=
    Classical.choice
      (exists_privateSecondNeighbour F v p hvp hvpMem hDegreeTwo)
  have hqz : q ≠ N.z := by
    intro h
    subst q
    apply hvqNotMem
    simpa using N.vz_mem
  have hvpPos : pos v ≠ pos p := fun h ↦ hvp (hpos h)
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  have hPointPMem :
      pos v - pos p ∈ LinearMap.range (localEquilibriumAt F pos v) :=
    namedNeighbourDifference_mem_localRange F pos v p hvp hvpMem
  have hPointZMem :
      pos v - pos N.z ∈ LinearMap.range (localEquilibriumAt F pos v) :=
    namedNeighbourDifference_mem_localRange F pos v N.z N.hvz N.vz_mem
  have hline : ∃ s : K,
      pos v = pos p + s • (pos N.z - pos p) := by
    apply exists_line_parameter_of_finrank_le_one
      (pos v) (pos p) (pos N.z)
      (LinearMap.range (localEquilibriumAt F pos v))
      hvpPos hpzPos hPointPMem hPointZMem
    change outsideLocalRank F pos v ≤ 1
    omega
  obtain ⟨s, hs⟩ := hline
  have hCollinearZ :
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) :=
    collinear_of_point_eq_line (pos v) (pos p) (pos N.z) s hs
  have hTrdegFinite := outsideExtensionTrdeg_lt_aleph0
    (k := k) pos v hgen
  have hTrdegOne : outsideExtensionTrdeg (k := k) pos v = 1 := by
    calc
      outsideExtensionTrdeg (k := k) pos v =
          ((outsideExtensionTrdeg (k := k) pos v).toNat : Cardinal) :=
        (Cardinal.cast_toNat_of_lt_aleph0 hTrdegFinite).symm
      _ = 1 := by
        change (d : Cardinal) = 1
        exact_mod_cast hdOne
  have hConnectingZero : deletedConnectingClass F pos v = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top]
    change outsideResponseKernelDim F pos v = outsideLocalKernelDim F pos v
    rw [hResponseOne, hKernelOne]
  exact ⟨N, hqz, hCollinearZ, hTrdegOne, hResponseOne,
    hKernelOne, hRankOne, hDegreeTwo, hConnectingZero⟩

/-- In the forced private exceptional shape,
the virtual row from the retained flag endpoint `p` to the second neighbour
`z` already lies in the literal child row space after deleting `v`.

The proof constructs the two-star relation, sends it through the actual
connecting map, identifies its away-load with a nonzero multiple of the
virtual row, and cancels that scalar. -/
theorem privateExceptional_virtualRow_mem
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ N : PrivateSecondNeighbour F v p,
      q ≠ N.z ∧
      PinCollinearity.Collinear (pos v) (pos p) (pos N.z) ∧
      directionRow pos (simpleEdge p N.z N.hpz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
  obtain ⟨N, hqz, hCollinearZ, _hTrdegOne, _hResponseOne,
      _hKernelOne, _hRankOne, _hDegreeTwo, hConnectingZero⟩ :=
    privateExceptional_classification (k := k) F pos v p q
      hvp hvq hpq hvpMem hvqNotMem hDegree hpos hcol hgen hExceptional
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  have hColPZV :
      PinCollinearity.Collinear (pos p) (pos N.z) (pos v) :=
    collinear_cycle (pos v) (pos p) (pos N.z) hCollinearZ
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (pos p) (pos N.z) (pos v) hpzPos).1 hColPZV
  have hsZero : s ≠ 0 := by
    intro hs0
    have hvpPos : pos v = pos p := by
      apply sub_eq_zero.mp
      simpa [hs0] using hs
    exact hvp (hpos hvpPos)
  have hsOne : s ≠ 1 := by
    intro hs1
    have hvzPos : pos v = pos N.z := by
      apply sub_eq_zero.mp
      have : pos v - pos N.z = 0 := by
        funext j
        have hj := congrFun hs j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        rw [hs1] at hj
        linear_combination hj
      exact this
    exact N.hvz (hpos hvzPos)
  have hScalar : s * (1 - s) ≠ 0 := by
    exact mul_ne_zero hsZero (sub_ne_zero.mpr (Ne.symm hsOne))
  let ep : incidentEdges F v :=
    ⟨simpleEdge v p hvp,
      mem_incidentEdges.mpr
        ⟨hvpMem, by rw [vertices_simpleEdge]; simp⟩⟩
  let ez : incidentEdges F v :=
    ⟨simpleEdge v N.z N.hvz,
      mem_incidentEdges.mpr
        ⟨N.vz_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let localWeight : incidentEdges F v → K :=
    Pi.single ep (1 - s) + Pi.single ez s
  have hLocalKernel : localEquilibriumAt F pos v localWeight = 0 := by
    change localEquilibriumAt F pos v
      (Pi.single ep (1 - s) + Pi.single ez s) = 0
    rw [map_add, localEquilibriumAt_piSingle,
      localEquilibriumAt_piSingle]
    change
      (1 - s) • directionRow pos (simpleEdge v p hvp) v +
          s • directionRow pos (simpleEdge v N.z N.hvz) v = 0
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left]
    funext j
    have hj := congrFun hs j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination hj
  let localRelation : LinearMap.ker (localEquilibriumAt F pos v) :=
    ⟨localWeight, hLocalKernel⟩
  have hClassZero :
      deletedConnectingClass F pos v localRelation = 0 := by
    rw [hConnectingZero]
    rfl
  have hAwayMem :=
    (deletedConnectingClass_eq_zero_iff F pos v localRelation).1 hClassZero
  have hFullLoad :
      directionEquilibrium (incidentEdges F v) pos localWeight =
        (s * (1 - s)) •
          directionRow pos (simpleEdge p N.z N.hpz) := by
    change directionEquilibrium (incidentEdges F v) pos
      (Pi.single ep (1 - s) + Pi.single ez s) = _
    rw [map_add, directionEquilibrium_piSingle,
      directionEquilibrium_piSingle]
    exact privateTwoStarRows_eq_virtualRow
      pos v p N.z hvp N.hvz N.hpz s hs
  have hScaledAway :
      restrictAway v
          ((s * (1 - s)) •
            directionRow pos (simpleEdge p N.z N.hpz)) ∈
        deletedAwayRowSpace F pos v := by
    change localToOldEquilibrium F pos v localWeight ∈
      deletedAwayRowSpace F pos v at hAwayMem
    change restrictAway v
      (directionEquilibrium (incidentEdges F v) pos localWeight) ∈
        deletedAwayRowSpace F pos v at hAwayMem
    rw [hFullLoad] at hAwayMem
    exact hAwayMem
  change restrictAway v
      ((s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz)) ∈
    (directionRowSpace (deleteVertexEdges F v) pos).map
      (restrictAway v) at hScaledAway
  obtain ⟨childLoad, hChildLoad, hChildRestrict⟩ :=
    Submodule.mem_map.mp hScaledAway
  have hChildAtV : childLoad v = 0 := by
    have hChildRange := hChildLoad
    rw [directionRowSpace_eq_range] at hChildRange
    obtain ⟨childWeight, hChildWeight⟩ := hChildRange
    rw [← hChildWeight]
    exact old_packet_equilibrium_at_deleted F pos v childWeight
  have hVirtualAtV :
      ((s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz)) v = 0 := by
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [congrFun
      (directionRow_simpleEdge_at_other pos p N.z v N.hpz hvp N.hvz) j]
    simp
  have hChildEq : childLoad =
      (s * (1 - s)) •
        directionRow pos (simpleEdge p N.z N.hpz) := by
    funext u
    by_cases huv : u = v
    · subst u
      rw [hChildAtV, hVirtualAtV]
    · have hu := congrFun hChildRestrict ⟨u, huv⟩
      exact hu
  have hScaledMem :
      (s * (1 - s)) •
          directionRow pos (simpleEdge p N.z N.hpz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
    rw [← hChildEq]
    exact hChildLoad
  have hVirtualMem :=
    (directionRowSpace (deleteVertexEdges F v) pos).smul_mem
      (s * (1 - s))⁻¹ hScaledMem
  have hCancel : (s * (1 - s))⁻¹ * (s * (1 - s)) = 1 :=
    inv_mul_cancel₀ hScalar
  refine ⟨N, hqz, hCollinearZ, ?_⟩
  simpa only [smul_smul, hCancel, one_smul] using hVirtualMem

omit [Fintype V] [DecidableEq V] in
/-- Two collinear triples sharing two distinct first points put the two
remaining points on one common line, with a nonzero affine parameter when
the new endpoint is distinct. -/
theorem exists_nonzero_line_parameter_of_common_collinear
    (x p q z : Fin 3 → K)
    (hxp : x ≠ p) (hpq : p ≠ q) (hpz : p ≠ z)
    (hxpq : PinCollinearity.Collinear x p q)
    (hxpz : PinCollinearity.Collinear x p z) :
    ∃ t : K, t ≠ 0 ∧ z - p = t • (q - p) := by
  obtain ⟨alpha, hq⟩ :=
    (collinear_iff_exists_smul_difference x p q hxp).1 hxpq
  obtain ⟨beta, hz⟩ :=
    (collinear_iff_exists_smul_difference x p z hxp).1 hxpz
  have hAlphaOne : alpha ≠ 1 := by
    intro h
    apply hpq
    have hqx : q - x = p - x := by
      simpa only [h, one_smul] using hq
    exact (sub_left_inj.mp hqx).symm
  have hAlphaSub : alpha - 1 ≠ 0 := sub_ne_zero.mpr hAlphaOne
  let t : K := (beta - 1) * (alpha - 1)⁻¹
  have hQP : q - p = (alpha - 1) • (p - x) := by
    funext j
    have hj := congrFun hq j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  have hZP : z - p = (beta - 1) • (p - x) := by
    funext j
    have hj := congrFun hz j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj
  have hline : z - p = t • (q - p) := by
    rw [hQP, hZP, smul_smul]
    have hScalar : t * (alpha - 1) = beta - 1 := by
      dsimp [t]
      rw [mul_assoc, inv_mul_cancel₀ hAlphaSub, mul_one]
    rw [hScalar]
  have ht : t ≠ 0 := by
    intro htZero
    apply hpz
    exact (sub_eq_zero.mp (by simpa [htZero] using hline)).symm
  exact ⟨t, ht, hline⟩

omit [Fintype V] in
/-- Scaled triangle-row identity for three collinear placed points.  The
identity is stated without division so cancellation is isolated in the
consumer. -/
theorem triangleRows_scaled_identity
    (pos : V → Fin 3 → K) (p q z : V)
    (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z) (t : K)
    (hline : pos z - pos p = t • (pos q - pos p)) :
    t • directionRow pos (simpleEdge q z hqz) =
      (t * (1 - t)) • directionRow pos (simpleEdge p q hpq) +
        (t - 1) • directionRow pos (simpleEdge p z hpz) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_other pos q z p hqz hpq hpz) j,
      congrFun (directionRow_simpleEdge_at_left pos p q hpq) j,
      congrFun (directionRow_simpleEdge_at_left pos p z hpz) j]
    have hj := congrFun hline j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hj ⊢
    linear_combination (t - 1) * hj
  · by_cases huq : u = q
    · subst u
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_left pos q z hqz) j,
        congrFun (directionRow_simpleEdge_at_right pos p q hpq) j,
        congrFun (directionRow_simpleEdge_at_other pos p z q hpz hpq.symm hqz) j]
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hj ⊢
      linear_combination -t * hj
    · by_cases huz : u = z
      · subst u
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos q z hqz) j,
          congrFun (directionRow_simpleEdge_at_other pos p q z hpq hpz.symm hqz.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos p z hpz) j]
        have hj := congrFun hline j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hj ⊢
        linear_combination hj
      · simp only [Pi.add_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other pos q z u hqz huq huz) j,
          congrFun (directionRow_simpleEdge_at_other pos p q u hpq hup huq) j,
          congrFun (directionRow_simpleEdge_at_other pos p z u hpz hup huz) j]
        simp

/-- If the other live terminal edge `pq` is
present, both possible response edges from the second neighbour lie in the
child row space. -/
theorem privateExceptional_bothVirtualRows_mem
    (F : SimpleEdgeSet V) (pos : V → Fin 3 → K) (v p q : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hpq : p ≠ q)
    (hvpMem : simpleEdge v p hvp ∈ F)
    (hpqMem : simpleEdge p q hpq ∈ F)
    (hvqNotMem : simpleEdge v q hvq ∉ F)
    (hDegree : edgeSetDegree F v ≤ 2)
    (hpos : Function.Injective pos)
    (hcol : PinCollinearity.Collinear (pos v) (pos p) (pos q))
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ pos c.1 c.2)) = ⊤)
    (hExceptional : PrivateExceptional (k := k) F pos v) :
    ∃ (N : PrivateSecondNeighbour F v p) (hqz : q ≠ N.z),
      directionRow pos (simpleEdge p N.z N.hpz) ∈
          directionRowSpace (deleteVertexEdges F v) pos ∧
      directionRow pos (simpleEdge q N.z hqz) ∈
          directionRowSpace (deleteVertexEdges F v) pos := by
  obtain ⟨N, hqz, hCollinearZ, hpzRow⟩ :=
    privateExceptional_virtualRow_mem (k := k) F pos v p q
      hvp hvq hpq hvpMem hvqNotMem hDegree hpos hcol hgen hExceptional
  have hvpPos : pos v ≠ pos p := fun h ↦ hvp (hpos h)
  have hpqPos : pos p ≠ pos q := fun h ↦ hpq (hpos h)
  have hpzPos : pos p ≠ pos N.z := fun h ↦ N.hpz (hpos h)
  obtain ⟨t, ht, hline⟩ :=
    exists_nonzero_line_parameter_of_common_collinear
      (pos v) (pos p) (pos q) (pos N.z)
      hvpPos hpqPos hpzPos hcol hCollinearZ
  have hpqDelete : simpleEdge p q hpq ∈ deleteVertexEdges F v := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨hpqMem, ?_⟩
    rw [vertices_simpleEdge]
    simp [hvp, hvq]
  have hpqRow : directionRow pos (simpleEdge p q hpq) ∈
      directionRowSpace (deleteVertexEdges F v) pos := by
    apply Submodule.subset_span
    exact ⟨⟨simpleEdge p q hpq, hpqDelete⟩, rfl⟩
  have hScaledRow :
      t • directionRow pos (simpleEdge q N.z hqz) ∈
        directionRowSpace (deleteVertexEdges F v) pos := by
    rw [triangleRows_scaled_identity pos p q N.z hpq N.hpz hqz t hline]
    exact (directionRowSpace (deleteVertexEdges F v) pos).add_mem
      ((directionRowSpace (deleteVertexEdges F v) pos).smul_mem _ hpqRow)
      ((directionRowSpace (deleteVertexEdges F v) pos).smul_mem _ hpzRow)
  have hRow :=
    (directionRowSpace (deleteVertexEdges F v) pos).smul_mem t⁻¹ hScaledRow
  have hCancel : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  have hqzRow : directionRow pos (simpleEdge q N.z hqz) ∈
      directionRowSpace (deleteVertexEdges F v) pos := by
    simpa only [smul_smul, hCancel, one_smul] using hRow
  exact ⟨N, hqz, hpzRow, hqzRow⟩

end

end DirectionStress

end RB31E2E
