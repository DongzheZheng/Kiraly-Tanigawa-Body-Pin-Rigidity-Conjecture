import RB31EndToEnd.Algebra.AffineSpanDescent
import RB31EndToEnd.Linear.OutsideLocalGeometry
import RB31EndToEnd.Linear.PrivateLocalClassification
import RB31EndToEnd.Linear.DirectionStressBaseChange
import RB31EndToEnd.Linear.DirectionResponseBaseChange

/-!
# Full response of the exceptional outside three-star

In the exceptional outside branch the deleted point contributes three
algebraically independent coordinates over the retained coordinate field.
The three retained neighbours are collinear, and the whole one-dimensional
local kernel has zero connecting class.

This file turns those already proved facts into the response statement
needed by the flag move: every one of the three neighbour-pair direction
rows belongs to the literal row space after deleting the apex.  The key
step is coefficient comparison over the retained coordinate field; no
response row is assumed as an input.
-/

namespace RB31E2E

namespace DirectionStress

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V]

open Set Submodule

/-! ## Retained-field models of the deleted row space -/

/-- Put all retained points in their coordinate field and put the deleted
vertex at zero.  The latter value is irrelevant to every deleted edge. -/
def retainedZeroPlacement
    (a : V → Fin 3 → K) (v : V) :
    V → Fin 3 → retainedCoordinateField (k := k) a v :=
  fun z j ↦ if hz : z = v then 0 else
    ⟨a z j, retained_coordinate_mem (k := k) a v z hz j⟩

omit [Fintype V] in
@[simp]
theorem retainedZeroPlacement_apply_of_ne
    (a : V → Fin 3 → K) (v z : V) (hz : z ≠ v) (j : Fin 3) :
    ((retainedZeroPlacement (k := k) a v z j :
      retainedCoordinateField (k := k) a v) : K) = a z j := by
  simp [retainedZeroPlacement, hz]

omit [Fintype V] in
/-- A deleted edge has exactly the same row after passing through the
retained-field zero model and extending scalars back to `K`. -/
theorem directionRow_map_retainedZeroPlacement_of_avoids
    (a : V → Fin 3 → K) (v : V) (e : SimpleEdge V)
    (hve : v ∉ e.vertices) :
    directionRow
        (mapPlacement (K := K) (retainedZeroPlacement (k := k) a v)) e =
      directionRow a e := by
  have hs : e.source ≠ v := by
    intro h
    apply hve
    rw [← h]
    rw [SimpleEdge.vertices, ← e.source_target_mk]
    simp [Sym2.toFinset_mk_eq]
  have ht : e.target ≠ v := by
    intro h
    apply hve
    rw [← h]
    rw [SimpleEdge.vertices, ← e.source_target_mk]
    simp [Sym2.toFinset_mk_eq]
  funext z j
  simp only [directionRow, edgeDirection, mapPlacement]
  split_ifs <;> simp [retainedZeroPlacement, hs, ht]

omit [Fintype V] in
/-- Hence the whole deleted row space is literally the scalar extension of
the retained-field deleted row space. -/
theorem directionRowSpace_map_retainedZeroPlacement_delete
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V) :
    directionRowSpace (deleteVertexEdges F v)
        (mapPlacement (K := K) (retainedZeroPlacement (k := k) a v)) =
      directionRowSpace (deleteVertexEdges F v) a := by
  unfold directionRowSpace
  congr 1
  ext row
  constructor <;> rintro ⟨e, rfl⟩
  · refine ⟨e, ?_⟩
    exact (directionRow_map_retainedZeroPlacement_of_avoids
      (k := k) a v e.1 (mem_deleteVertexEdges.mp e.2).2).symm
  · refine ⟨e, ?_⟩
    exact directionRow_map_retainedZeroPlacement_of_avoids
      (k := k) a v e.1 (mem_deleteVertexEdges.mp e.2).2

omit [Fintype V] [DecidableEq V] in
/-- Flattening a nested finite load is a linear equivalence, so it
preserves membership in the span of a labelled row family. -/
theorem flattenVector_mem_span_iff
    {I : Type*} [Finite I]
    (row : I → V → Fin 3 → k) (z : V → Fin 3 → k) :
    flattenVector z ∈
        span k (Set.range (fun i ↦ flattenVector (row i))) ↔
      z ∈ span k (Set.range row) := by
  let flat : (V → Fin 3 → k) ≃ₗ[k] (V × Fin 3 → k) :=
    (LinearEquiv.curry k k V (Fin 3)).symm
  have hset : flat '' Set.range row =
      Set.range (fun i ↦ flattenVector (row i)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨row i, ⟨i, rfl⟩, rfl⟩
  have hspan :
      (span k (Set.range row)).map
          (flat : (V → Fin 3 → k) →ₗ[k] (V × Fin 3 → k)) =
        span k (Set.range (fun i ↦ flattenVector (row i))) := by
    rw [Submodule.map_span]
    change span k (flat '' Set.range row) = _
    rw [hset]
  rw [← hspan]
  constructor
  · intro hz
    obtain ⟨y, hy, hflat⟩ := Submodule.mem_map.mp hz
    have : y = z := flat.injective hflat
    simpa [this] using hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-! ## Affine coefficient loads -/

/-- Insert a spatial vector as the load at one named vertex. -/
def vertexLoad (p : V) (z : Fin 3 → k) : V → Fin 3 → k :=
  Pi.single p z

/-- The spatial coordinate basis vector. -/
def coordinateUnit (j : Fin 3) : Fin 3 → k :=
  Pi.single j 1

/-- Constant term of the away-load of the collinear three-star. -/
def outsideAwayConstant
    (pos : V → Fin 3 → k) (p q r : V) (t : k) :
    V → Fin 3 → k :=
  (1 - t) • vertexLoad p (pos p) +
    t • vertexLoad q (pos q) - vertexLoad r (pos r)

/-- Coefficient of an arbitrary apex vector in the same away-load. -/
def outsideAwayCoefficient
    (p q r : V) (t : k) (z : Fin 3 → k) :
    V → Fin 3 → k :=
  -(1 - t) • vertexLoad p z -
    t • vertexLoad q z + vertexLoad r z

omit [Fintype V] in
/-- The arbitrary-vector coefficient is the linear combination of its
three coordinate coefficients. -/
theorem outsideAwayCoefficient_eq_sum_coordinateUnit
    (p q r : V) (t : k) (z : Fin 3 → k) :
    outsideAwayCoefficient p q r t z =
      ∑ j : Fin 3, z j •
        outsideAwayCoefficient p q r t (coordinateUnit j) := by
  funext u c
  by_cases hup : u = p <;> by_cases huq : u = q <;>
      by_cases hur : u = r <;> fin_cases c <;>
    simp_all [outsideAwayCoefficient, vertexLoad, coordinateUnit,
      Pi.single_apply, Fin.sum_univ_three] <;> ring

omit [Fintype V] in
/-- First coefficient identity: constant plus the coefficient evaluated at
the third point is the `pq` direction row, up to the nonzero scalar
`t(1-t)`. -/
theorem outsideAwayConstant_add_coefficient_r
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos r) =
      (t * (1 - t)) • directionRow pos (simpleEdge p q hpq) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos p q hpq) j]
    have hj := congrFun hline j
    simp [vertexLoad, hpq, hpr] at hj ⊢
    linear_combination -(1 - t) * hj
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos p q hpq) j]
      have hj := congrFun hline j
      simp [vertexLoad, hpq, hqr] at hj ⊢
      linear_combination -t * hj
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p q r hpq hpr.symm hqr.symm) j]
        simp [vertexLoad, hpr, hqr]
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p q u hpq hup huq) j]
        simp [vertexLoad, hup, huq, hur]

omit [Fintype V] in
/-- Second coefficient identity, stated without division. -/
theorem outsideAway_one_sub_t_smul_constant_add_coefficient_p
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    (1 - t) • (outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos p)) =
      t • directionRow pos (simpleEdge q r hqr) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun
      (directionRow_simpleEdge_at_other pos q r p hqr hpq hpr) j]
    simp [vertexLoad, hpq, hpr]
    exact Or.inr (by ring)
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_left pos q r hqr) j]
      have hj := congrFun hline j
      simp [vertexLoad, hpq, hqr] at hj ⊢
      linear_combination t * hj
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos q r hqr) j]
        have hj := congrFun hline j
        simp [vertexLoad, hpr, hqr] at hj ⊢
        linear_combination -hj
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos q r u hqr huq hur) j]
        simp [vertexLoad, hup, huq, hur]

omit [Fintype V] in
/-- Third coefficient identity, again with all denominators cleared. -/
theorem outsideAway_t_smul_constant_add_coefficient_q
    (pos : V → Fin 3 → k) (p q r : V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    t • (outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos q)) =
      (1 - t) • directionRow pos (simpleEdge p r hpr) := by
  funext u j
  by_cases hup : u = p
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos p r hpr) j]
    have hj := congrFun hline j
    simp [vertexLoad, hpq, hpr] at hj ⊢
    linear_combination (1 - t) * hj
  · by_cases huq : u = q
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun
        (directionRow_simpleEdge_at_other pos p r q hpr hpq.symm hqr) j]
      simp [vertexLoad, hpq, hqr]
    · by_cases hur : u = r
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_right pos p r hpr) j]
        have hj := congrFun hline j
        simp [vertexLoad, hpr, hqr] at hj ⊢
        linear_combination -hj
      · simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun
          (directionRow_simpleEdge_at_other pos p r u hpr hup hur) j]
        simp [vertexLoad, hup, huq, hur]

/-! ## Scalar extension and the three-star away-load -/

omit [Fintype V] in
/-- Scalar extension commutes with the constant away-load. -/
theorem mapPlacement_outsideAwayConstant
    {L : Type*} [Field L] [Algebra L K]
    (pos : V → Fin 3 → L) (p q r : V) (t : L) :
    mapPlacement (K := K) (outsideAwayConstant pos p q r t) =
      outsideAwayConstant (mapPlacement (K := K) pos) p q r
        (algebraMap L K t) := by
  funext z j
  by_cases hzp : z = p <;> by_cases hzq : z = q <;>
      by_cases hzr : z = r <;>
    simp_all [mapPlacement, outsideAwayConstant, vertexLoad,
      map_sub, map_one, map_mul, Algebra.smul_def]

omit [Fintype V] in
/-- Scalar extension commutes with every linear away coefficient. -/
theorem mapPlacement_outsideAwayCoefficient
    {L : Type*} [Field L] [Algebra L K]
    (p q r : V) (t : L) (z : Fin 3 → L) :
    mapPlacement (K := K) (outsideAwayCoefficient p q r t z) =
      outsideAwayCoefficient p q r (algebraMap L K t)
        (fun j ↦ algebraMap L K (z j)) := by
  funext u j
  by_cases hup : u = p <;> by_cases huq : u = q <;>
      by_cases hur : u = r <;>
    simp_all [mapPlacement, outsideAwayCoefficient, vertexLoad,
      map_sub, map_one, map_mul, Algebra.smul_def]

omit [Fintype V] in
/-- A coordinate basis vector is fixed by scalar extension. -/
theorem map_coordinateUnit
    {L : Type*} [Field L] [Algebra L K] (j : Fin 3) :
    (fun c ↦ algebraMap L K (coordinateUnit (k := L) j c)) =
      coordinateUnit (k := K) j := by
  funext c
  simp [coordinateUnit, Pi.single_apply]

omit [Fintype V] in
/-- The affine constant plus its value at the apex is exactly the away-load
of the fixed local relation `(1-t,t,-1)`.  Collinearity is needed only at
the apex, where it says that this relation is locally equilibrated. -/
theorem outsideAwayConstant_add_coefficient_eq_threeStar
    (pos : V → Fin 3 → k) (v p q r : V)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : k)
    (hline : pos r - pos p = t • (pos q - pos p)) :
    outsideAwayConstant pos p q r t +
        outsideAwayCoefficient p q r t (pos v) =
      (1 - t) • directionRow pos (simpleEdge v p hvp) +
        t • directionRow pos (simpleEdge v q hvq) +
        (-1 : k) • directionRow pos (simpleEdge v r hvr) := by
  funext u j
  by_cases huv : u = v
  · subst u
    simp only [outsideAwayConstant, outsideAwayCoefficient,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [congrFun (directionRow_simpleEdge_at_left pos v p hvp) j,
      congrFun (directionRow_simpleEdge_at_left pos v q hvq) j,
      congrFun (directionRow_simpleEdge_at_left pos v r hvr) j]
    have hj := congrFun hline j
    simp [vertexLoad, hvp, hvq, hvr] at hj ⊢
    linear_combination -hj
  · by_cases hup : u = p
    · subst u
      simp only [outsideAwayConstant, outsideAwayCoefficient,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [congrFun (directionRow_simpleEdge_at_right pos v p hvp) j,
        congrFun (directionRow_simpleEdge_at_other
          pos v q p hvq hvp.symm hpq) j,
        congrFun (directionRow_simpleEdge_at_other
          pos v r p hvr hvp.symm hpr) j]
      simp [vertexLoad, hpq, hpr]
      ring
    · by_cases huq : u = q
      · subst u
        simp only [outsideAwayConstant, outsideAwayCoefficient,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
        rw [congrFun (directionRow_simpleEdge_at_other
            pos v p q hvp hvq.symm hpq.symm) j,
          congrFun (directionRow_simpleEdge_at_right pos v q hvq) j,
          congrFun (directionRow_simpleEdge_at_other
            pos v r q hvr hvq.symm hqr) j]
        simp [vertexLoad, hpq, hqr]
        ring
      · by_cases hur : u = r
        · subst u
          simp only [outsideAwayConstant, outsideAwayCoefficient,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
          rw [congrFun (directionRow_simpleEdge_at_other
              pos v p r hvp hvr.symm hpr.symm) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v q r hvq hvr.symm hqr.symm) j,
            congrFun (directionRow_simpleEdge_at_right pos v r hvr) j]
          simp [vertexLoad, hpr, hqr]
          ring
        · simp only [outsideAwayConstant, outsideAwayCoefficient,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
          rw [congrFun (directionRow_simpleEdge_at_other
              pos v p u hvp huv hup) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v q u hvq huv huq) j,
            congrFun (directionRow_simpleEdge_at_other
              pos v r u hvr huv hur) j]
          simp [vertexLoad, hup, huq, hur]

omit [Fintype V] [DecidableEq V] in
/-- Collinearity of three scalar-extended points descends to the smaller
field when two of the points are distinct. -/
theorem collinear_restrictScalars_for_response
    {L : Type*} [Field L] [Algebra L K]
    (p q r : Fin 3 → L) (hpq : p ≠ q)
    (hcol : PinCollinearity.Collinear
      (fun j ↦ algebraMap L K (p j))
      (fun j ↦ algebraMap L K (q j))
      (fun j ↦ algebraMap L K (r j))) :
    PinCollinearity.Collinear p q r := by
  have hpqK : (fun j ↦ algebraMap L K (p j)) ≠
      (fun j ↦ algebraMap L K (q j)) := by
    intro h
    apply hpq
    funext j
    exact (RingHom.injective (algebraMap L K)) (congrFun h j)
  obtain ⟨s, hs⟩ :=
    (collinear_iff_exists_smul_difference
      (fun j ↦ algebraMap L K (p j))
      (fun j ↦ algebraMap L K (q j))
      (fun j ↦ algebraMap L K (r j)) hpqK).1 hcol
  have hCoordinate : ∃ j : Fin 3, q j - p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    funext j
    exact sub_eq_zero.mp (h j) |>.symm
  obtain ⟨j, hj⟩ := hCoordinate
  let t : L := (r j - p j) / (q j - p j)
  have hsEq : s = algebraMap L K t := by
    have hsj := congrFun hs j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsj
    have hjK : algebraMap L K (q j - p j) ≠ 0 := by
      intro hzero
      apply hj
      apply RingHom.injective (algebraMap L K)
      simpa using hzero
    have htMul : t * (q j - p j) = r j - p j := by
      exact div_mul_cancel₀ (r j - p j) hj
    have hmap := congrArg (algebraMap L K) htMul
    simp only [map_mul, map_sub] at hmap
    apply mul_right_cancel₀ hjK
    calc
      s * algebraMap L K (q j - p j) =
          algebraMap L K (r j - p j) := by
        simpa only [map_sub] using hsj.symm
      _ = algebraMap L K t * algebraMap L K (q j - p j) := by
        simpa only [map_sub] using hmap.symm
  apply (collinear_iff_exists_smul_difference p q r hpq).2
  refine ⟨t, ?_⟩
  funext i
  apply (RingHom.injective (algebraMap L K))
  have hi := congrFun hs i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  rw [map_mul, map_sub]
  rw [← hsEq]
  simpa only [map_sub] using hi

set_option maxHeartbeats 800000 in
/-- **PF outside full response.**  A genuinely exceptional degree-at-most
three outside star forces all three virtual neighbour rows into the child
row space.  The returned packet is the packet produced by the literal
exceptional classification. -/
theorem outsideExceptional_fullResponse
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) (v : V)
    (ha : Function.Injective a)
    (hDegree : edgeSetDegree F v ≤ 3)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun c : V × Fin 3 ↦ a c.1 c.2)) = ⊤)
    (hExceptional : OutsideExceptional (k := k) F a v) :
    ∃ N : DegreeThreeNeighbours F v,
      edgeSetDegree F v = 3 ∧
      outsideExtensionTrdeg (k := k) a v = 3 ∧
      outsideResponseKernelDim F a v = 1 ∧
      PinCollinearity.Collinear (a N.p) (a N.q) (a N.r) ∧
      directionRow a (simpleEdge N.p N.q N.hpq) ∈
          directionRowSpace (deleteVertexEdges F v) a ∧
      directionRow a (simpleEdge N.p N.r N.hpr) ∈
          directionRowSpace (deleteVertexEdges F v) a ∧
      directionRow a (simpleEdge N.q N.r N.hqr) ∈
          directionRowSpace (deleteVertexEdges F v) a := by
  obtain ⟨N, hCollinear, hpqA, hprA, hqrA, hTrdegThree,
      hResponseOne, hKernelOne, hRankTwo, hConnectingZero⟩ :=
    outsideExceptional_classification (k := k) F a v ha hDegree hgen hExceptional
  have hDegreeThree : edgeSetDegree F v = 3 := by
    have hRankNullity := outsideLocalRank_add_kernelDim_eq_degree F a v
    rw [hRankTwo, hKernelOne] at hRankNullity
    omega
  let L : IntermediateField k K := retainedCoordinateField (k := k) a v
  let b : V → Fin 3 → L := retainedZeroPlacement (k := k) a v
  have hbp : (fun j ↦ algebraMap L K (b N.p j)) = a N.p := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.p N.hvp.symm j
  have hbq : (fun j ↦ algebraMap L K (b N.q j)) = a N.q := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.q N.hvq.symm j
  have hbr : (fun j ↦ algebraMap L K (b N.r j)) = a N.r := by
    funext j
    exact retainedZeroPlacement_apply_of_ne
      (k := k) a v N.r N.hvr.symm j
  have hbpq : b N.p ≠ b N.q := by
    intro h
    apply N.hpq
    apply ha
    rw [← hbp, ← hbq, h]
  have hCollinearL :
      PinCollinearity.Collinear (b N.p) (b N.q) (b N.r) := by
    apply collinear_restrictScalars_for_response
      (K := K) (b N.p) (b N.q) (b N.r) hbpq
    simpa only [hbp, hbq, hbr] using hCollinear
  obtain ⟨t, hline⟩ :=
    (collinear_iff_exists_smul_difference
      (b N.p) (b N.q) (b N.r) hbpq).1 hCollinearL
  have htZero : t ≠ 0 := by
    intro ht
    have hEqL : b N.r = b N.p := by
      funext j
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj
      rw [ht] at hj
      simp only [zero_mul] at hj
      linear_combination hj
    apply N.hpr
    apply ha
    rw [← hbp, ← hbr, hEqL]
  have htOne : t ≠ 1 := by
    intro ht
    have hEqL : b N.r = b N.q := by
      funext j
      have hj := congrFun hline j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj
      rw [ht] at hj
      simp only [one_mul] at hj
      linear_combination hj
    apply N.hqr
    apply ha
    rw [← hbq, ← hbr, hEqL]
  have hOneSub : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htOne)
  have hIndependent : AlgebraicIndependent L (deletedCoordinates a v) := by
    apply deletedCoordinates_algebraicIndependent_of_three_le_trdeg
      (k := k) a v
    · exact adjoin_retained_union_deleted_eq_top (k := k) a v hgen
    · rw [hTrdegThree]
  let ep : incidentEdges F v :=
    ⟨simpleEdge v N.p N.hvp,
      mem_incidentEdges.mpr
        ⟨N.vp_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let eq : incidentEdges F v :=
    ⟨simpleEdge v N.q N.hvq,
      mem_incidentEdges.mpr
        ⟨N.vq_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let er : incidentEdges F v :=
    ⟨simpleEdge v N.r N.hvr,
      mem_incidentEdges.mpr
        ⟨N.vr_mem, by rw [vertices_simpleEdge]; simp⟩⟩
  let localWeight : incidentEdges F v → K :=
    Pi.single ep (algebraMap L K (1 - t)) +
      Pi.single eq (algebraMap L K t) + Pi.single er (-1)
  have hLineK : a N.r - a N.p =
      algebraMap L K t • (a N.q - a N.p) := by
    rw [← hbp, ← hbq, ← hbr]
    funext j
    have hj := congrFun hline j
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
      using congrArg (algebraMap L K) hj
  have hLocalKernel : localEquilibriumAt F a v localWeight = 0 := by
    change localEquilibriumAt F a v
      (Pi.single ep (algebraMap L K (1 - t)) +
        Pi.single eq (algebraMap L K t) + Pi.single er (-1)) = 0
    rw [map_add, map_add, localEquilibriumAt_piSingle,
      localEquilibriumAt_piSingle, localEquilibriumAt_piSingle]
    change
      algebraMap L K (1 - t) •
          directionRow a (simpleEdge v N.p N.hvp) v +
        algebraMap L K t •
          directionRow a (simpleEdge v N.q N.hvq) v +
        (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) v = 0
    rw [directionRow_simpleEdge_at_left,
      directionRow_simpleEdge_at_left, directionRow_simpleEdge_at_left]
    funext j
    have hj := congrFun hLineK j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_sub, map_one, Pi.zero_apply] at hj ⊢
    linear_combination hj
  let localRelation : LinearMap.ker (localEquilibriumAt F a v) :=
    ⟨localWeight, hLocalKernel⟩
  have hClassZero : deletedConnectingClass F a v localRelation = 0 := by
    rw [hConnectingZero]
    rfl
  have hAwayMem :=
    (deletedConnectingClass_eq_zero_iff F a v localRelation).1 hClassZero
  let fullLoad : V → Fin 3 → K :=
    directionEquilibrium (incidentEdges F v) a localWeight
  have hFullAtV : fullLoad v = 0 := by
    exact hLocalKernel
  have hFullMem : fullLoad ∈ directionRowSpace (deleteVertexEdges F v) a := by
    change localToOldEquilibrium F a v localWeight ∈
      deletedAwayRowSpace F a v at hAwayMem
    change restrictAway v fullLoad ∈
      (directionRowSpace (deleteVertexEdges F v) a).map (restrictAway v)
      at hAwayMem
    obtain ⟨childLoad, hChildLoad, hChildRestrict⟩ :=
      Submodule.mem_map.mp hAwayMem
    have hChildAtV : childLoad v = 0 := by
      have hChildRange := hChildLoad
      rw [directionRowSpace_eq_range] at hChildRange
      obtain ⟨childWeight, rfl⟩ := hChildRange
      exact old_packet_equilibrium_at_deleted F a v childWeight
    have hEq : childLoad = fullLoad := by
      funext z
      by_cases hz : z = v
      · subst z
        rw [hChildAtV, hFullAtV]
      · exact congrFun hChildRestrict ⟨z, hz⟩
    rwa [← hEq]
  let constant : V → Fin 3 → L :=
    outsideAwayConstant b N.p N.q N.r t
  let coefficient : Fin 3 → V → Fin 3 → L :=
    fun j ↦ outsideAwayCoefficient N.p N.q N.r t (coordinateUnit j)
  have hFullFormula : fullLoad =
      algebraMap L K (1 - t) • directionRow a (simpleEdge v N.p N.hvp) +
        algebraMap L K t • directionRow a (simpleEdge v N.q N.hvq) +
        (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) := by
    change directionEquilibrium (incidentEdges F v) a
      (Pi.single ep (algebraMap L K (1 - t)) +
        Pi.single eq (algebraMap L K t) + Pi.single er (-1)) = _
    rw [map_add, map_add, directionEquilibrium_piSingle,
      directionEquilibrium_piSingle, directionEquilibrium_piSingle]
  have hbp' : mapPlacement (K := K) b N.p = a N.p := hbp
  have hbq' : mapPlacement (K := K) b N.q = a N.q := hbq
  have hbr' : mapPlacement (K := K) b N.r = a N.r := hbr
  have hMapConstant : mapPlacement (K := K) constant =
      outsideAwayConstant a N.p N.q N.r (algebraMap L K t) := by
    calc
      mapPlacement (K := K) constant =
          outsideAwayConstant (mapPlacement (K := K) b)
            N.p N.q N.r (algebraMap L K t) := by
        exact mapPlacement_outsideAwayConstant
          (K := K) b N.p N.q N.r t
      _ = outsideAwayConstant a N.p N.q N.r (algebraMap L K t) := by
        unfold outsideAwayConstant
        rw [hbp', hbq', hbr']
  have hMapCoefficient (j : Fin 3) :
      mapPlacement (K := K) (coefficient j) =
        outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
          (coordinateUnit (k := K) j) := by
    calc
      mapPlacement (K := K) (coefficient j) =
          outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
            (fun c ↦ algebraMap L K (coordinateUnit (k := L) j c)) := by
        exact mapPlacement_outsideAwayCoefficient
          (K := K) N.p N.q N.r t (coordinateUnit j)
      _ = outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
          (coordinateUnit (k := K) j) := by
        rw [map_coordinateUnit (K := K) (L := L) j]
  have hAffineIdentity :
      mapPlacement (K := K) constant +
          ∑ j : Fin 3, deletedCoordinates a v j •
            mapPlacement (K := K) (coefficient j) = fullLoad := by
    calc
      mapPlacement (K := K) constant +
            ∑ j : Fin 3, deletedCoordinates a v j •
              mapPlacement (K := K) (coefficient j) =
          outsideAwayConstant a N.p N.q N.r (algebraMap L K t) +
            ∑ j : Fin 3, deletedCoordinates a v j •
              outsideAwayCoefficient N.p N.q N.r (algebraMap L K t)
                (coordinateUnit j) := by
        rw [hMapConstant]
        congr 1
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hMapCoefficient j]
      _ = outsideAwayConstant a N.p N.q N.r (algebraMap L K t) +
          outsideAwayCoefficient N.p N.q N.r (algebraMap L K t) (a v) := by
        congr 1
        simpa only [deletedCoordinates] using
          (outsideAwayCoefficient_eq_sum_coordinateUnit
            N.p N.q N.r (algebraMap L K t) (a v)).symm
      _ = algebraMap L K (1 - t) •
            directionRow a (simpleEdge v N.p N.hvp) +
          algebraMap L K t • directionRow a (simpleEdge v N.q N.hvq) +
          (-1 : K) • directionRow a (simpleEdge v N.r N.hvr) := by
        simpa only [map_sub, map_one] using
          (outsideAwayConstant_add_coefficient_eq_threeStar
            a v N.p N.q N.r N.hvp N.hvq N.hvr
              N.hpq N.hpr N.hqr (algebraMap L K t) hLineK)
      _ = fullLoad := hFullFormula.symm
  have hAffineMemCurried :
      mapPlacement (K := K) constant +
          ∑ j : Fin 3, deletedCoordinates a v j •
            mapPlacement (K := K) (coefficient j) ∈
        directionRowSpace (deleteVertexEdges F v)
          (mapPlacement (K := K) b) := by
    rw [hAffineIdentity,
      directionRowSpace_map_retainedZeroPlacement_delete (k := k)]
    exact hFullMem
  have hAffineMemFlat :
      FiniteFamilyBaseChange.mapVector (K := K) (flattenVector constant) +
          ∑ j : Fin 3, deletedCoordinates a v j •
            FiniteFamilyBaseChange.mapVector (K := K)
              (flattenVector (coefficient j)) ∈
        span K (Set.range (fun e : deleteVertexEdges F v ↦
          FiniteFamilyBaseChange.mapVector (K := K)
            (flattenVector (directionRow b e.1)))) := by
    have hFlat := (flattenVector_mem_span_iff
      (k := K)
      (fun e : deleteVertexEdges F v ↦
        directionRow (mapPlacement (K := K) b) e.1)
      (mapPlacement (K := K) constant +
        ∑ j : Fin 3, deletedCoordinates a v j •
          mapPlacement (K := K) (coefficient j))).2
      (by simpa [directionRowSpace] using hAffineMemCurried)
    simpa only [flattenVector, mapPlacement,
      FiniteFamilyBaseChange.mapVector, Function.comp_apply,
      Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
      directionRow_mapPlacement] using hFlat
  have hDescended := AffineSpanDescent.affineCoefficients_mem_span
    (K := K)
    (fun e : deleteVertexEdges F v ↦ flattenVector (directionRow b e.1))
    (deletedCoordinates a v) hIndependent
    (flattenVector constant)
    (fun j ↦ flattenVector (coefficient j)) hAffineMemFlat
  let W : Submodule L (V × Fin 3 → L) :=
    span L (Set.range (fun e : deleteVertexEdges F v ↦
      flattenVector (directionRow b e.1)))
  have hConstant : flattenVector constant ∈ W := hDescended.1
  have hCoefficient : ∀ j, flattenVector (coefficient j) ∈ W :=
    hDescended.2
  have coefficientMem (z : Fin 3 → L) :
      flattenVector (outsideAwayCoefficient N.p N.q N.r t z) ∈ W := by
    let term : Fin 3 → (V × Fin 3 → L) :=
      fun j x ↦ z j * flattenVector (coefficient j) x
    have hFlatSum :
        flattenVector (outsideAwayCoefficient N.p N.q N.r t z) =
          ∑ j : Fin 3, term j := by
      rw [outsideAwayCoefficient_eq_sum_coordinateUnit]
      funext x
      simp only [flattenVector, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, term, coefficient]
    rw [hFlatSum]
    apply W.sum_mem
    intro j _hj
    have hj := W.smul_mem (z j) (hCoefficient j)
    simpa only [term, Pi.smul_apply, smul_eq_mul] using hj
  have hpqFlat :
      flattenVector (directionRow b (simpleEdge N.p N.q N.hpq)) ∈ W := by
    have hScaled := W.add_mem hConstant (coefficientMem (b N.r))
    change flattenVector
      (outsideAwayConstant b N.p N.q N.r t +
        outsideAwayCoefficient N.p N.q N.r t (b N.r)) ∈ W at hScaled
    rw [outsideAwayConstant_add_coefficient_r
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline] at hScaled
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.p N.q N.hpq))
    change (fun x : V × Fin 3 ↦ (t * (1 - t)) * row x) ∈ W at hScaled
    have h := W.smul_mem (t * (1 - t))⁻¹ hScaled
    change (fun x : V × Fin 3 ↦
      (t * (1 - t))⁻¹ * ((t * (1 - t)) * row x)) ∈ W at h
    have hScalar : t * (1 - t) ≠ 0 := mul_ne_zero htZero hOneSub
    have hCancel : (fun x : V × Fin 3 ↦
        (t * (1 - t))⁻¹ * ((t * (1 - t)) * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ hScalar, one_mul]
    rw [hCancel] at h
    exact h
  have hqrFlat :
      flattenVector (directionRow b (simpleEdge N.q N.r N.hqr)) ∈ W := by
    have hScaled := W.smul_mem (1 - t)
      (W.add_mem hConstant (coefficientMem (b N.p)))
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.q N.r N.hqr))
    have hId := outsideAway_one_sub_t_smul_constant_add_coefficient_p
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline
    have hFlatId : (fun x : V × Fin 3 ↦
        (1 - t) * (flattenVector constant x +
          flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.p)) x)) =
        (fun x : V × Fin 3 ↦ t * row x) := by
      funext x
      exact congrFun (congrFun hId x.1) x.2
    change (fun x : V × Fin 3 ↦
      (1 - t) * (flattenVector constant x +
        flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.p)) x)) ∈ W
      at hScaled
    rw [hFlatId] at hScaled
    have h := W.smul_mem t⁻¹ hScaled
    change (fun x : V × Fin 3 ↦ t⁻¹ * (t * row x)) ∈ W at h
    have hCancel : (fun x : V × Fin 3 ↦ t⁻¹ * (t * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ htZero, one_mul]
    rw [hCancel] at h
    exact h
  have hprFlat :
      flattenVector (directionRow b (simpleEdge N.p N.r N.hpr)) ∈ W := by
    have hScaled := W.smul_mem t
      (W.add_mem hConstant (coefficientMem (b N.q)))
    let row : V × Fin 3 → L :=
      flattenVector (directionRow b (simpleEdge N.p N.r N.hpr))
    have hId := outsideAway_t_smul_constant_add_coefficient_q
      b N.p N.q N.r N.hpq N.hpr N.hqr t hline
    have hFlatId : (fun x : V × Fin 3 ↦
        t * (flattenVector constant x +
          flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.q)) x)) =
        (fun x : V × Fin 3 ↦ (1 - t) * row x) := by
      funext x
      exact congrFun (congrFun hId x.1) x.2
    change (fun x : V × Fin 3 ↦
      t * (flattenVector constant x +
        flattenVector (outsideAwayCoefficient N.p N.q N.r t (b N.q)) x)) ∈ W
      at hScaled
    rw [hFlatId] at hScaled
    have h := W.smul_mem (1 - t)⁻¹ hScaled
    change (fun x : V × Fin 3 ↦ (1 - t)⁻¹ * ((1 - t) * row x)) ∈ W at h
    have hCancel : (fun x : V × Fin 3 ↦
        (1 - t)⁻¹ * ((1 - t) * row x)) = row := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ hOneSub, one_mul]
    rw [hCancel] at h
    exact h
  have hpqL : directionRow b (simpleEdge N.p N.q N.hpq) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.p N.q N.hpq))).1
    exact hpqFlat
  have hprL : directionRow b (simpleEdge N.p N.r N.hpr) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.p N.r N.hpr))).1
    exact hprFlat
  have hqrL : directionRow b (simpleEdge N.q N.r N.hqr) ∈
      directionRowSpace (deleteVertexEdges F v) b := by
    apply (flattenVector_mem_span_iff
      (fun e : deleteVertexEdges F v ↦ directionRow b e.1)
      (directionRow b (simpleEdge N.q N.r N.hqr))).1
    exact hqrFlat
  have hpqK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.p N.q N.hpq) hpqL
  have hprK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.p N.r N.hpr) hprL
  have hqrK := directionRow_mem_mapPlacement_of_mem
    (K := K) (deleteVertexEdges F v) b
    (simpleEdge N.q N.r N.hqr) hqrL
  rw [directionRowSpace_map_retainedZeroPlacement_delete (k := k)] at hpqK hprK hqrK
  have hpqRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.p N.q N.hpq) =
      directionRow a (simpleEdge N.p N.q N.hpq) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvp, N.hvq]
  have hprRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.p N.r N.hpr) =
      directionRow a (simpleEdge N.p N.r N.hpr) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvp, N.hvr]
  have hqrRow : directionRow
      (mapPlacement (K := K) b) (simpleEdge N.q N.r N.hqr) =
      directionRow a (simpleEdge N.q N.r N.hqr) := by
    apply directionRow_map_retainedZeroPlacement_of_avoids (k := k)
    simp [vertices_simpleEdge, N.hvq, N.hvr]
  rw [hpqRow] at hpqK
  rw [hprRow] at hprK
  rw [hqrRow] at hqrK
  exact ⟨N, hDegreeThree, hTrdegThree, hResponseOne,
    hCollinear, hpqK, hprK, hqrK⟩

end

end DirectionStress

end RB31E2E
