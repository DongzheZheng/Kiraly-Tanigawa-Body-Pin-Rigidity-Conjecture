import RB31EndToEnd.Combinatorics.Sparse22.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Direction rows and their stress space

For a finite simple edge set `F` and a placement `a : V → k³`, this file
defines the transpose of the ordinary three-dimensional direction matrix as
an explicit linear map

`(F → k) →ₗ[k] (V → Fin 3 → k)`.

Its kernel is the direction-stress space used by the provenance-flag
induction.  The orientation chosen for an unordered edge is bookkeeping
only: a direction row has opposite endpoint loads, so reversing the
orientation leaves the row unchanged.  No sparsity, genericity,
semismallness, or height assertion is made here.
-/

namespace RB31E2E

namespace SimpleEdge

noncomputable section

variable {V : Type*}

/-- A bookkeeping source for an unordered simple edge. -/
def source (e : SimpleEdge V) : V :=
  e.1.out.1

/-- A bookkeeping target for an unordered simple edge. -/
def target (e : SimpleEdge V) : V :=
  e.1.out.2

/-- The chosen ordered endpoints recover the original unordered pair. -/
theorem source_target_mk (e : SimpleEdge V) :
    s(e.source, e.target) = e.1 :=
  Quot.out_eq e.1

/-- The two oriented endpoints of a simple edge are distinct. -/
theorem source_ne_target (e : SimpleEdge V) : e.source ≠ e.target := by
  intro h
  apply e.2
  rw [← e.source_target_mk, Sym2.mk_isDiag_iff]
  exact h

end


end SimpleEdge

namespace DirectionStress

noncomputable section

variable {k V : Type*} [Field k] [Fintype V] [DecidableEq V]

/-- The oriented difference vector carried by one simple edge. -/
def edgeDirection (a : V → Fin 3 → k) (e : SimpleEdge V) : Fin 3 → k :=
  fun j ↦ a e.source j - a e.target j

/--
The direction row of one edge, viewed as a load on all vertex-coordinate
blocks.  It is `a_source - a_target` at the source, its negative at the
target, and zero elsewhere.
-/
def directionRow (a : V → Fin 3 → k) (e : SimpleEdge V) :
    V → Fin 3 → k :=
  fun v j ↦
    (if e.source = v then edgeDirection a e j else 0) +
      (if e.target = v then -(edgeDirection a e j) else 0)

omit [Fintype V] in
@[simp]
theorem directionRow_source (a : V → Fin 3 → k) (e : SimpleEdge V) :
    directionRow a e e.source = edgeDirection a e := by
  funext j
  simp [directionRow, Ne.symm e.source_ne_target]

omit [Fintype V] in
@[simp]
theorem directionRow_target (a : V → Fin 3 → k) (e : SimpleEdge V) :
    directionRow a e e.target = -(edgeDirection a e) := by
  funext j
  simp [directionRow, e.source_ne_target]

omit [Fintype V] in
theorem directionRow_eq_zero_of_ne
    (a : V → Fin 3 → k) (e : SimpleEdge V) (v : V)
    (hsource : e.source ≠ v) (htarget : e.target ≠ v) :
    directionRow a e v = 0 := by
  funext j
  simp [directionRow, hsource, htarget]

/-- One coordinate of the endpoint-equilibrium load of edge weights. -/
def directionEquilibriumCoordinate
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (weight : F → k) (v : V) (j : Fin 3) : k :=
  ∑ e : F, weight e * directionRow a e.1 v j

/--
The transpose of the direction matrix.  It sends edge weights to the three
equilibrium coordinates at every vertex.
-/
def directionEquilibrium
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    (F → k) →ₗ[k] (V → Fin 3 → k) where
  toFun weight v j := directionEquilibriumCoordinate F a weight v j
  map_add' x y := by
    funext v j
    simp only [directionEquilibriumCoordinate, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [add_mul]
  map_smul' c x := by
    funext v j
    simp only [directionEquilibriumCoordinate, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [RingHom.id_apply, mul_assoc]

omit [Fintype V] in
@[simp]
theorem directionEquilibrium_apply
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k)
    (weight : F → k) (v : V) (j : Fin 3) :
    directionEquilibrium F a weight v j =
      directionEquilibriumCoordinate F a weight v j :=
  rfl

omit [Fintype V] in
/-- The equilibrium map is literally the linear combination of edge rows. -/
theorem directionEquilibrium_eq_sum_smul_directionRow
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) :
    directionEquilibrium F a weight =
      ∑ e : F, weight e • directionRow a e.1 := by
  funext v j
  change (∑ e : F, weight e * directionRow a e.1 v j) =
    (∑ e : F, weight e • directionRow a e.1) v j
  simp

omit [Fintype V] in
/-- The range of the equilibrium synthesis map is exactly the span of the
labelled direction rows. -/
theorem range_directionEquilibrium_eq_span_directionRows
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    LinearMap.range (directionEquilibrium F a) =
      Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1)) := by
  apply le_antisymm
  · rintro y ⟨weight, rfl⟩
    rw [directionEquilibrium_eq_sum_smul_directionRow]
    exact Submodule.sum_mem _ fun e _ ↦
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self e))
  · rw [Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    let weight : F → k := Pi.single e 1
    refine ⟨weight, ?_⟩
    rw [directionEquilibrium_eq_sum_smul_directionRow]
    change (∑ x ∈ F.attach,
      Pi.single e 1 x • directionRow a x.1) = directionRow a e.1
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hbe
      simp [hbe]
    · intro he
      exact (he (Finset.mem_attach F e)).elim

/-- Pointwise equilibrium, with every vertex and spatial coordinate visible. -/
def IsDirectionStress
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) : Prop :=
  ∀ v j, directionEquilibriumCoordinate F a weight v j = 0

/-- The actual direction-stress vector space. -/
abbrev DirectionStressSpace
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :=
  LinearMap.ker (directionEquilibrium F a)

omit [Fintype V] in
/-- Pointwise equilibrium is exactly membership in the explicit kernel. -/
theorem isDirectionStress_iff_mem
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) (weight : F → k) :
    IsDirectionStress F a weight ↔ weight ∈ DirectionStressSpace F a := by
  constructor
  · intro h
    rw [LinearMap.mem_ker]
    funext v j
    exact h v j
  · intro h v j
    rw [LinearMap.mem_ker] at h
    have hv := congrFun (congrFun h v) j
    simpa using hv

/-- The finite dimension of the direction-stress space. -/
def directionStressDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) : ℕ :=
  Module.finrank k (DirectionStressSpace F a)

/-- The row rank of the direction matrix, read from its synthesis map. -/
def directionEquilibriumRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) : ℕ :=
  Module.finrank k (LinearMap.range (directionEquilibrium F a))

omit [Fintype V] in
/-- Row rank as the dimension of the span of the literal direction-row
family. -/
theorem directionEquilibriumRank_eq_finrank_span_rows
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a =
      Module.finrank k
        (Submodule.span k (Set.range (fun e : F ↦ directionRow a e.1))) := by
  rw [directionEquilibriumRank,
    range_directionEquilibrium_eq_span_directionRows]

/-- Rank--nullity with the edge-set cardinality kept explicit. -/
theorem directionEquilibriumRank_add_directionStressDim
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionEquilibriumRank F a + directionStressDim F a = F.card := by
  have h := (directionEquilibrium F a).finrank_range_add_finrank_ker
  have hdomain : Module.finrank k (F → k) = F.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  simpa [directionEquilibriumRank, directionStressDim,
    DirectionStressSpace, hdomain] using h

/-- The same rank--nullity identity with stress dimension first. -/
theorem directionStressDim_add_directionEquilibriumRank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a + directionEquilibriumRank F a = F.card := by
  simpa [add_comm] using
    directionEquilibriumRank_add_directionStressDim F a

/-- Stress dimension never exceeds the number of live edges. -/
theorem directionStressDim_le_card
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a ≤ F.card := by
  calc
    directionStressDim F a ≤
        directionStressDim F a + directionEquilibriumRank F a :=
      Nat.le_add_right _ _
    _ = F.card := directionStressDim_add_directionEquilibriumRank F a

/-- Stress dimension is edge cardinality minus direction-row rank. -/
theorem directionStressDim_eq_card_sub_rank
    (F : SimpleEdgeSet V) (a : V → Fin 3 → k) :
    directionStressDim F a = F.card - directionEquilibriumRank F a :=
  Nat.eq_sub_of_add_eq (directionStressDim_add_directionEquilibriumRank F a)

end

end DirectionStress

end RB31E2E
