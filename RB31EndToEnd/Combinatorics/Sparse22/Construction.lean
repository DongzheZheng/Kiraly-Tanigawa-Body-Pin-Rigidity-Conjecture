import RB31EndToEnd.Combinatorics.Sparse22.TightCompletion

/-!
# Nixon--Owen reductions for simple `(2,2)`-tight graphs

This file gives literal edge-set semantics to the four inverse moves in
Nixon--Owen's construction theorem: inverse Henneberg 1, inverse
Henneberg 2, `K₄`-to-vertex, and `K₃`-to-edge.  A graph is represented by
an ambient simple edge set together with its active vertex set.  The
`SupportedOn` condition is load bearing: `Tight22 F X` alone only counts
the edges of `F` induced by `X` and does not rule out edges outside `X`.

The first reduction branch is closed below: deleting any degree-two
vertex of a supported `(2,2)`-tight graph produces a strictly smaller
supported `(2,2)`-tight graph.  The full Nixon--Owen reduction disjunction
additionally needs the degree-three admissibility and triangle-sequence
arguments.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- Every edge of `F` has both endpoints in the active vertex set `X`. -/
def SupportedOn (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  ∀ ⦃e : SimpleEdge V⦄, e ∈ F → e.vertices ⊆ X

/-- A simple `(2,2)`-tight graph on an explicit active vertex set. -/
structure SimpleTight22On (F : SimpleEdgeSet V) (X : Finset V) : Prop where
  supported : SupportedOn F X
  sparse : Sparse22 F
  tight : Tight22 F X

theorem edgesInside_eq_self_of_supported {F : SimpleEdgeSet V} {X : Finset V}
    (hF : SupportedOn F X) : edgesInside F X = F := by
  ext e
  simp only [mem_edgesInside]
  constructor
  · exact And.left
  · intro he
    exact ⟨he, hF he⟩

/-- Edges incident with `v`. -/
def incidentEdges (F : SimpleEdgeSet V) (v : V) : SimpleEdgeSet V :=
  F.filter fun e => v ∈ e.vertices

/-- The degree of `v` in the simple edge set `F`. -/
def edgeSetDegree (F : SimpleEdgeSet V) (v : V) : ℕ :=
  (incidentEdges F v).card

/-- Delete `v` and every edge incident with it. -/
def deleteVertexEdges (F : SimpleEdgeSet V) (v : V) : SimpleEdgeSet V :=
  F.filter fun e => v ∉ e.vertices

@[simp]
theorem mem_incidentEdges {F : SimpleEdgeSet V} {v : V} {e : SimpleEdge V} :
    e ∈ incidentEdges F v ↔ e ∈ F ∧ v ∈ e.vertices := by
  simp [incidentEdges]

@[simp]
theorem mem_deleteVertexEdges {F : SimpleEdgeSet V} {v : V} {e : SimpleEdge V} :
    e ∈ deleteVertexEdges F v ↔ e ∈ F ∧ v ∉ e.vertices := by
  simp [deleteVertexEdges]

theorem deleteVertexEdges_subset (F : SimpleEdgeSet V) (v : V) :
    deleteVertexEdges F v ⊆ F := by
  intro e he
  exact (mem_deleteVertexEdges.mp he).1

theorem incidentEdges_disjoint_deleteVertexEdges (F : SimpleEdgeSet V) (v : V) :
    Disjoint (incidentEdges F v) (deleteVertexEdges F v) := by
  rw [Finset.disjoint_left]
  intro e heIncident heDelete
  exact (mem_deleteVertexEdges.mp heDelete).2 (mem_incidentEdges.mp heIncident).2

theorem incidentEdges_union_deleteVertexEdges (F : SimpleEdgeSet V) (v : V) :
    incidentEdges F v ∪ deleteVertexEdges F v = F := by
  ext e
  by_cases hev : v ∈ e.vertices <;> simp [hev]

theorem card_incidentEdges_add_card_deleteVertexEdges
    (F : SimpleEdgeSet V) (v : V) :
    (incidentEdges F v).card + (deleteVertexEdges F v).card = F.card := by
  rw [← Finset.card_union_of_disjoint
    (incidentEdges_disjoint_deleteVertexEdges F v)]
  rw [incidentEdges_union_deleteVertexEdges]

theorem deleteVertexEdges_supported {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    SupportedOn (deleteVertexEdges F v) (X.erase v) := by
  intro e he y hy
  have heF := (mem_deleteVertexEdges.mp he).1
  have hvNot := (mem_deleteVertexEdges.mp he).2
  rw [Finset.mem_erase]
  exact ⟨fun hyv => hvNot (hyv ▸ hy), hF heF hy⟩

theorem edgesInside_deleteVertexEdges_erase {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    edgesInside (deleteVertexEdges F v) (X.erase v) = deleteVertexEdges F v :=
  edgesInside_eq_self_of_supported (deleteVertexEdges_supported hF)

theorem edgesInside_erase_eq_deleteVertexEdges
    {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hF : SupportedOn F X) :
    edgesInside F (X.erase v) = deleteVertexEdges F v := by
  ext e
  simp only [mem_edgesInside, mem_deleteVertexEdges]
  constructor
  · rintro ⟨heF, heX⟩
    refine ⟨heF, ?_⟩
    intro hv
    exact (Finset.mem_erase.mp (heX hv)).1 rfl
  · rintro ⟨heF, hv⟩
    refine ⟨heF, ?_⟩
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyv => hv (hyv ▸ hy), hF heF hy⟩

theorem edgesInside_deleteVertexEdges_erase_eq
    (F : SimpleEdgeSet V) (Y : Finset V) (v : V) :
    edgesInside (deleteVertexEdges F v) (Y.erase v) =
      edgesInside (deleteVertexEdges F v) Y := by
  ext e
  simp only [mem_edgesInside, mem_deleteVertexEdges]
  constructor
  · rintro ⟨⟨heF, hvNot⟩, heY⟩
    exact ⟨⟨heF, hvNot⟩, heY.trans (Finset.erase_subset v Y)⟩
  · rintro ⟨⟨heF, hvNot⟩, heY⟩
    refine ⟨⟨heF, hvNot⟩, ?_⟩
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyv => hvNot (hyv ▸ hy), heY hy⟩

/-- A tight blocking set in a vertex-deleted graph cannot contain the deleted vertex. -/
theorem not_mem_of_tight22_deleteVertexEdges
    {F : SimpleEdgeSet V} {Y : Finset V} {v a : V}
    (hSparse : Sparse22 (deleteVertexEdges F v))
    (hTight : Tight22 (deleteVertexEdges F v) Y)
    (haY : a ∈ Y) (hva : v ≠ a) :
    v ∉ Y := by
  intro hvY
  have hEraseNonempty : (Y.erase v).Nonempty :=
    ⟨a, Finset.mem_erase.mpr ⟨Ne.symm hva, haY⟩⟩
  have hUpper := hSparse (Y.erase v) hEraseNonempty
  rw [edgesInside_deleteVertexEdges_erase_eq F Y v, hTight.2] at hUpper
  have hEraseCard := Finset.card_erase_of_mem hvY
  have hYcardTwo : 2 ≤ Y.card := by
    exact Finset.one_lt_card.mpr ⟨v, hvY, a, haY, hva⟩
  omega

/--
Exact local degree bookkeeping: after adjoining `v` to a set `Y` not
containing it, the induced edges split into the incident edges at `v` and
the old vertex-deleted induced edges, provided all incident edges land in
`insert v Y`.
-/
theorem card_edgesInside_insert_eq_degree_add
    (F : SimpleEdgeSet V) (Y : Finset V) (v : V) (hvY : v ∉ Y)
    (hIncident : SupportedOn (incidentEdges F v) (insert v Y)) :
    (edgesInside F (insert v Y)).card =
      edgeSetDegree F v + (edgesInside (deleteVertexEdges F v) Y).card := by
  have hSplit :
      edgesInside F (insert v Y) =
        edgesInside (incidentEdges F v) (insert v Y) ∪
          edgesInside (deleteVertexEdges F v) (insert v Y) := by
    ext e
    simp only [mem_edgesInside, mem_incidentEdges, mem_deleteVertexEdges,
      Finset.mem_union]
    constructor
    · rintro ⟨heF, heZ⟩
      by_cases hev : v ∈ e.vertices
      · exact Or.inl ⟨⟨heF, hev⟩, heZ⟩
      · exact Or.inr ⟨⟨heF, hev⟩, heZ⟩
    · rintro (⟨⟨heF, _hev⟩, heZ⟩ | ⟨⟨heF, _hev⟩, heZ⟩) <;>
        exact ⟨heF, heZ⟩
  have hDeleteInside :
      edgesInside (deleteVertexEdges F v) (insert v Y) =
        edgesInside (deleteVertexEdges F v) Y := by
    ext e
    simp only [mem_edgesInside, mem_deleteVertexEdges]
    constructor
    · rintro ⟨⟨heF, hev⟩, heZ⟩
      refine ⟨⟨heF, hev⟩, ?_⟩
      intro y hy
      have hyZ := heZ hy
      rw [Finset.mem_insert] at hyZ
      rcases hyZ with rfl | hyY
      · exact (hev hy).elim
      · exact hyY
    · rintro ⟨he, heY⟩
      exact ⟨he, heY.trans (Finset.subset_insert v Y)⟩
  have hDisjoint :
      Disjoint (edgesInside (incidentEdges F v) (insert v Y))
        (edgesInside (deleteVertexEdges F v) (insert v Y)) := by
    rw [Finset.disjoint_left]
    intro e heIncident heDelete
    exact (mem_deleteVertexEdges.mp (mem_edgesInside.mp heDelete).1).2
      (mem_incidentEdges.mp (mem_edgesInside.mp heIncident).1).2
  rw [hSplit, Finset.card_union_of_disjoint hDisjoint,
    edgesInside_eq_self_of_supported hIncident, hDeleteInside]
  rfl

/-- A simple edge with ordered input and unordered output. -/
def simpleEdge (a b : V) (hab : a ≠ b) : SimpleEdge V :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff]⟩

@[simp]
theorem vertices_simpleEdge (a b : V) (hab : a ≠ b) :
    (simpleEdge a b hab).vertices = {a, b} := by
  simp [simpleEdge, SimpleEdge.vertices, Sym2.toFinset_mk_eq]

omit [DecidableEq V] in
@[simp]
theorem simpleEdge_eq_simpleEdge_iff
    (a b c d : V) (hab : a ≠ b) (hcd : c ≠ d) :
    simpleEdge a b hab = simpleEdge c d hcd ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [simpleEdge, Subtype.mk.injEq, Sym2.eq_iff]

omit [DecidableEq V] in
theorem simpleEdge_comm (a b : V) (hab : a ≠ b) :
    simpleEdge a b hab = simpleEdge b a (Ne.symm hab) := by
  apply Subtype.ext
  simp [simpleEdge]

theorem sym2_eq_of_toFinset_eq
    {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hvertices : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
          have hab : a ≠ b := by
            simpa [Sym2.mk_isDiag_iff] using he
          have hcd : c ≠ d := by
            simpa [Sym2.mk_isDiag_iff] using hf
          have ha : a = c ∨ a = d := by
            have : a ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          have hb : b = c ∨ b = d := by
            have : b ∈ s(c, d).toFinset := by
              rw [← hvertices]
              simp
            simpa [Sym2.toFinset_mk_eq] using this
          rw [Sym2.eq_iff]
          rcases ha with hac | had <;> rcases hb with hbc | hbd
          · exact (hab (hac.trans hbc.symm)).elim
          · exact Or.inl ⟨hac, hbd⟩
          · exact Or.inr ⟨had, hbc⟩
          · exact (hab (had.trans hbd.symm)).elim

theorem SimpleEdge.eq_of_vertices_eq {e f : SimpleEdge V}
    (hvertices : e.vertices = f.vertices) : e = f := by
  apply Subtype.ext
  exact sym2_eq_of_toFinset_eq e.2 f.2 hvertices

/-- An incident simple edge has a unique other endpoint. -/
theorem exists_otherEndpoint (e : SimpleEdge V) {v : V}
    (hv : v ∈ e.vertices) :
    ∃ a : V, ∃ hva : v ≠ a, e = simpleEdge v a hva := by
  obtain ⟨a, ha, hav⟩ :=
    Finset.exists_mem_ne (by simp : 1 < e.vertices.card) v
  have hva : v ≠ a := Ne.symm hav
  have hPairSubset : {v, a} ⊆ e.vertices := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hv
    · exact ha
  have hPairCard : ({v, a} : Finset V).card = 2 := by simp [hva]
  have hVertices : e.vertices = {v, a} := by
    exact (Finset.eq_of_subset_of_card_le hPairSubset (by
      rw [hPairCard, e.card_vertices])).symm
  have hEdgeEq : e = simpleEdge v a hva := by
    apply SimpleEdge.eq_of_vertices_eq
    rw [hVertices, vertices_simpleEdge]
  exact ⟨a, hva, hEdgeEq⟩

/-- `F` contains every simple edge whose endpoints lie in `K`. -/
def IsCliqueEdgeSet (F : SimpleEdgeSet V) (K : Finset V) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, ∀ hab : a ≠ b, simpleEdge a b hab ∈ F

/-- Four named vertices, with all six simple edges, form a copy of `K₄`. -/
structure NamedK4Witness
    (F : SimpleEdgeSet V) (v a b c : V) : Prop where
  hva : v ≠ a
  hvb : v ≠ b
  hvc : v ≠ c
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  va_mem : simpleEdge v a hva ∈ F
  vb_mem : simpleEdge v b hvb ∈ F
  vc_mem : simpleEdge v c hvc ∈ F
  ab_mem : simpleEdge a b hab ∈ F
  ac_mem : simpleEdge a c hac ∈ F
  bc_mem : simpleEdge b c hbc ∈ F

/-- Three named distinct neighbours exhaust a degree-three incidence set. -/
theorem incidentEdges_eq_three
    {F : SimpleEdgeSet V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    incidentEdges F v =
      {simpleEdge v a hva, simpleEdge v b hvb, simpleEdge v c hvc} := by
  let S : SimpleEdgeSet V :=
    {simpleEdge v a hva, simpleEdge v b hvb, simpleEdge v c hvc}
  have hSsub : S ⊆ incidentEdges F v := by
    intro e he
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact mem_incidentEdges.mpr ⟨hvaF, by simp⟩
    · exact mem_incidentEdges.mpr ⟨hvbF, by simp⟩
    · exact mem_incidentEdges.mpr ⟨hvcF, by simp⟩
  have hScard : S.card = 3 := by
    simp [S, hvb, hvc, hab, hac, hbc]
  have hIncidentCard : (incidentEdges F v).card = 3 := hDegree
  exact (Finset.eq_of_subset_of_card_le hSsub (by omega)).symm

/--
`F'` is the simple push-forward of `F` along `φ`.  Edges mapped to loops
have no witness in the simple target type, and coincident images are merged
by the set semantics.  Thus legality below detects precisely when a
contraction remains a simple tight graph.
-/
def IsSimpleEdgePushForward (φ : V → V)
    (F F' : SimpleEdgeSet V) : Prop :=
  ∀ e' : SimpleEdge V,
    e' ∈ F' ↔ ∃ e : SimpleEdge V, e ∈ F ∧ e'.1 = e.1.map φ

/-- Collapse all vertices of `K` to its retained representative `r`. -/
def collapseSet (K : Finset V) (r : V) (x : V) : V :=
  if x ∈ K then r else x

/-- Merge `b` into the retained vertex `a`. -/
def mergeVertex (a b x : V) : V :=
  if x = b then a else x

/-- The exact graph surgery underlying an inverse Henneberg 1 move. -/
def IsInverseHennebergOne
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ v : V,
    v ∈ X ∧ edgeSetDegree F v = 2 ∧
      X' = X.erase v ∧ F' = deleteVertexEdges F v

/-- The exact graph surgery underlying an inverse Henneberg 2 move. -/
def IsInverseHennebergTwo
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ v a b : V, ∃ hva : v ≠ a, ∃ hvb : v ≠ b, ∃ hab : a ≠ b,
    v ∈ X ∧ a ∈ X ∧ b ∈ X ∧
      edgeSetDegree F v = 3 ∧
      simpleEdge v a hva ∈ F ∧ simpleEdge v b hvb ∈ F ∧
      simpleEdge a b hab ∉ F ∧
      X' = X.erase v ∧
      F' = insert (simpleEdge a b hab) (deleteVertexEdges F v)

/--
The exact `K₄`-to-vertex contraction, inverse to vertex-to-`K₄`.
The representative `r` stays active; the other three clique vertices are
removed.  Parallel images are collapsed, so the separate legality predicate
below is essential.
-/
def IsInverseVertexToK4
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ K : Finset V, ∃ r : V,
    K.card = 4 ∧ K ⊆ X ∧ r ∈ K ∧ IsCliqueEdgeSet F K ∧
      X' = insert r (X \ K) ∧
      IsSimpleEdgePushForward (collapseSet K r) F F'

/-- Three distinct vertices span all three edges of a triangle. -/
def IsTriangleEdgeSet (F : SimpleEdgeSet V) (u a b : V) : Prop :=
  ∃ hua : u ≠ a, ∃ hub : u ≠ b, ∃ hab : a ≠ b,
    simpleEdge u a hua ∈ F ∧
      simpleEdge u b hub ∈ F ∧ simpleEdge a b hab ∈ F

/--
The exact `K₃`-to-edge contraction, inverse to edge-to-`K₃`: in the
triangle on `u,a,b`, vertex `b` is merged into `a`.  The two edges to `u`
coalesce to the retained edge and `ab` becomes a loop and disappears.
-/
def IsInverseEdgeToK3
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  ∃ u a b : V,
    u ∈ X ∧ a ∈ X ∧ b ∈ X ∧ IsTriangleEdgeSet F u a b ∧
      X' = X.erase b ∧
      IsSimpleEdgePushForward (mergeVertex a b) F F'

/-- An inverse Henneberg 1 move whose output remains simple `(2,2)`-tight. -/
def LegalInverseHennebergOne
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseHennebergOne F X F' X' ∧ SimpleTight22On F' X'

/-- An inverse Henneberg 2 move whose output remains simple `(2,2)`-tight. -/
def LegalInverseHennebergTwo
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseHennebergTwo F X F' X' ∧ SimpleTight22On F' X'

/-- An allowable `K₄`-to-vertex move. -/
def LegalInverseVertexToK4
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseVertexToK4 F X F' X' ∧ SimpleTight22On F' X'

/-- An allowable `K₃`-to-edge move. -/
def LegalInverseEdgeToK3
    (F : SimpleEdgeSet V) (X : Finset V)
    (F' : SimpleEdgeSet V) (X' : Finset V) : Prop :=
  IsInverseEdgeToK3 F X F' X' ∧ SimpleTight22On F' X'

/-- The literal four-way reduction conclusion of Nixon--Owen Lemma 3.11. -/
def HasNixonOwenReduction (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  ∃ F' : SimpleEdgeSet V, ∃ X' : Finset V,
    X'.card < X.card ∧
      (LegalInverseHennebergOne F X F' X' ∨
        LegalInverseHennebergTwo F X F' X' ∨
        LegalInverseVertexToK4 F X F' X' ∨
        LegalInverseEdgeToK3 F X F' X')

/-- The exact `K₄` base object, including its complete-edge semantics. -/
def IsK4Base (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  X.card = 4 ∧ SimpleTight22On F X ∧ IsCliqueEdgeSet F X

theorem IsInverseHennebergOne.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseHennebergOne F X F' X') :
    X'.card < X.card := by
  obtain ⟨v, hv, _hDegree, rfl, _hEdges⟩ := h
  rw [Finset.card_erase_of_mem hv]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)

theorem IsInverseHennebergTwo.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseHennebergTwo F X F' X') :
    X'.card < X.card := by
  obtain ⟨v, _a, _b, _hva, _hvb, _hab, hv, _ha, _hb, _hDegree,
    _hvaF, _hvbF, _habF, rfl, _hEdges⟩ := h
  rw [Finset.card_erase_of_mem hv]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)

theorem IsInverseVertexToK4.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseVertexToK4 F X F' X') :
    X'.card < X.card := by
  obtain ⟨K, r, hKcard, hKX, hrK, _hClique, rfl, _hPush⟩ := h
  have hrNot : r ∉ X \ K := by simp [hrK]
  rw [Finset.card_insert_of_notMem hrNot,
    Finset.card_sdiff_of_subset hKX, hKcard]
  have hFourLe : 4 ≤ X.card := by
    rw [← hKcard]
    exact Finset.card_le_card hKX
  omega

theorem IsInverseEdgeToK3.card_lt
    {F F' : SimpleEdgeSet V} {X X' : Finset V}
    (h : IsInverseEdgeToK3 F X F' X') :
    X'.card < X.card := by
  obtain ⟨_u, _a, b, _hu, _ha, hb, _hTriangle, rfl, _hPush⟩ := h
  rw [Finset.card_erase_of_mem hb]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨b, hb⟩) (by decide)

/-- Every vertex of a supported tight graph with at least two vertices has degree at least two. -/
theorem two_le_edgeSetDegree_of_simpleTight22On
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hXcard : 2 ≤ X.card) :
    2 ≤ edgeSetDegree F v := by
  have hEraseNonempty : (X.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcardZero : (X.erase v).card = 0 := by simp [hEmpty]
    rw [Finset.card_erase_of_mem hv] at hcardZero
    omega
  have hSparseErase := hG.sparse (X.erase v) hEraseNonempty
  rw [edgesInside_erase_eq_deleteVertexEdges hG.supported] at hSparseErase
  have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hEraseCard := Finset.card_erase_of_mem hv
  unfold edgeSetDegree
  omega

/-- Handshaking for an edge set supported on its active vertex set. -/
theorem sum_edgeSetDegree_eq_twice_card
    {F : SimpleEdgeSet V} {X : Finset V} (hF : SupportedOn F X) :
    (∑ v ∈ X, edgeSetDegree F v) = 2 * F.card := by
  classical
  have hDegreeAsSum (v : V) :
      edgeSetDegree F v =
        ∑ e ∈ F, if v ∈ e.vertices then 1 else 0 := by
    rw [edgeSetDegree, incidentEdges, Finset.card_eq_sum_ones,
      Finset.sum_filter]
  calc
    (∑ v ∈ X, edgeSetDegree F v) =
        ∑ v ∈ X, ∑ e ∈ F, if v ∈ e.vertices then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hDegreeAsSum v
    _ = ∑ e ∈ F, ∑ v ∈ X, if v ∈ e.vertices then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ F, e.vertices.card := by
      apply Finset.sum_congr rfl
      intro e he
      have hfilter : X.filter (fun v => v ∈ e.vertices) = e.vertices := by
        ext v
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun hv => hF he hv)
      calc
        (∑ v ∈ X, if v ∈ e.vertices then 1 else 0) =
            (X.filter fun v => v ∈ e.vertices).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = e.vertices.card := congrArg Finset.card hfilter
    _ = ∑ _e ∈ F, 2 := by simp
    _ = 2 * F.card := by simp [Nat.mul_comm]

/-- Every nonempty supported tight graph has a vertex of degree at most three. -/
theorem exists_edgeSetDegree_le_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X) :
    ∃ v ∈ X, edgeSetDegree F v ≤ 3 := by
  by_contra hNoLow
  push Not at hNoLow
  have hLower :
      ∑ v ∈ X, 4 ≤ ∑ v ∈ X, edgeSetDegree F v := by
    exact Finset.sum_le_sum fun v hv => hNoLow v hv
  have hHandshake := sum_edgeSetDegree_eq_twice_card hG.supported
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hXpos : 0 < X.card := Finset.card_pos.mpr hG.tight.1
  have hLower' :
      4 * X.card ≤ ∑ v ∈ X, edgeSetDegree F v := by
    simpa [Nat.mul_comm] using hLower
  rw [hHandshake, hTotal] at hLower'
  omega

/-- On at least two vertices, the low-degree vertex has degree exactly two or three. -/
theorem exists_edgeSetDegree_eq_two_or_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    ∃ v ∈ X, edgeSetDegree F v = 2 ∨ edgeSetDegree F v = 3 := by
  obtain ⟨v, hv, hUpper⟩ := exists_edgeSetDegree_le_three hG
  have hLower := two_le_edgeSetDegree_of_simpleTight22On hG hv hXcard
  exact ⟨v, hv, by omega⟩

/--
The degree-two branch of the Nixon--Owen reduction theorem.  No
admissibility hypothesis is needed: mere deletion preserves sparsity, and
the exact two-edge loss preserves tightness.
-/
theorem legalInverseHennebergOne_of_degree_two
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hDegree : edgeSetDegree F v = 2) :
    LegalInverseHennebergOne F X
      (deleteVertexEdges F v) (X.erase v) := by
  refine ⟨⟨v, hv, hDegree, rfl, rfl⟩, ?_⟩
  refine ⟨deleteVertexEdges_supported hG.supported,
    hG.sparse.mono (deleteVertexEdges_subset F v), ?_⟩
  have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
  have hTotal : F.card = 2 * (X.card - 1) := by
    rw [← edgesInside_eq_self_of_supported hG.supported]
    exact hG.tight.2
  have hEraseCard := Finset.card_erase_of_mem hv
  have hDeleteCard :
      (deleteVertexEdges F v).card = 2 * ((X.erase v).card - 1) := by
    unfold edgeSetDegree at hDegree
    omega
  have hEraseNonempty : (X.erase v).Nonempty := by
    apply Finset.card_pos.mp
    unfold edgeSetDegree at hDegree
    omega
  refine ⟨hEraseNonempty, ?_⟩
  rw [edgesInside_deleteVertexEdges_erase hG.supported]
  exact hDeleteCard

/--
Once a missing pair of neighbours is known to be admissible for sparsity,
the inverse Henneberg 2 surgery automatically has the correct global count
and active-vertex support.
-/
theorem legalInverseHennebergTwo_of_sparse_insert
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hSparse :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))) :
    LegalInverseHennebergTwo F X
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) := by
  refine ⟨?_, ?_⟩
  · exact ⟨v, a, b, hva, hvb, hab, hvX, haX, hbX, hDegree,
      hvaF, hvbF, habF, rfl, rfl⟩
  · refine ⟨?_, hSparse, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | heDelete
      · rw [vertices_simpleEdge]
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩
        · exact Finset.mem_erase.mpr ⟨Ne.symm hvb, hbX⟩
      · exact deleteVertexEdges_supported hG.supported heDelete
    · have hCandidateDelete :
          simpleEdge a b hab ∉ deleteVertexEdges F v := by
        intro he
        exact habF (deleteVertexEdges_subset F v he)
      have hPartition := card_incidentEdges_add_card_deleteVertexEdges F v
      have hTotal : F.card = 2 * (X.card - 1) := by
        rw [← edgesInside_eq_self_of_supported hG.supported]
        exact hG.tight.2
      have hEraseCard := Finset.card_erase_of_mem hvX
      have hResultCard :
          (insert (simpleEdge a b hab) (deleteVertexEdges F v)).card =
            2 * ((X.erase v).card - 1) := by
        rw [Finset.card_insert_of_notMem hCandidateDelete]
        unfold edgeSetDegree at hDegree
        omega
      refine ⟨⟨a, Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩⟩, ?_⟩
      rw [edgesInside_eq_self_of_supported]
      · exact hResultCard
      · intro e he
        rw [Finset.mem_insert] at he
        rcases he with rfl | heDelete
        · rw [vertices_simpleEdge]
          intro y hy
          rw [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨Ne.symm hva, haX⟩
          · exact Finset.mem_erase.mpr ⟨Ne.symm hvb, hbX⟩
        · exact deleteVertexEdges_supported hG.supported heDelete

/--
Failure of a proposed inverse Henneberg 2 edge is witnessed by a tight
set in the vertex-deleted graph containing both proposed endpoints.  This
is the exact obstruction consumed by the Nixon--Owen uncrossing argument.
-/
theorem exists_tight22_obstruction_of_not_hennebergTwo_admissible
    {F : SimpleEdgeSet V} {v a b : V} (hva : v ≠ a) (hab : a ≠ b)
    (hSparseDelete : Sparse22 (deleteVertexEdges F v))
    (habF : simpleEdge a b hab ∉ F)
    (hBad :
      ¬ Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))) :
    ∃ Y : Finset V,
      Y.Nonempty ∧ a ∈ Y ∧ b ∈ Y ∧ v ∉ Y ∧
        Tight22 (deleteVertexEdges F v) Y := by
  have habDelete : simpleEdge a b hab ∉ deleteVertexEdges F v := by
    intro he
    exact habF (deleteVertexEdges_subset F v he)
  obtain ⟨Y, hYne, hedgeY, hYtight⟩ :=
    exists_tight22_of_not_sparse22_insert hSparseDelete habDelete hBad
  have habVertices : (simpleEdge a b hab).vertices = {a, b} :=
    vertices_simpleEdge a b hab
  rw [habVertices] at hedgeY
  have haY : a ∈ Y := hedgeY (by simp)
  have hbY : b ∈ Y := hedgeY (by simp)
  have hvY : v ∉ Y :=
    not_mem_of_tight22_deleteVertexEdges hSparseDelete hYtight haY hva
  exact ⟨Y, hYne, haY, hbY, hvY, hYtight⟩

/--
Provenance-preserving degree-three dichotomy for one proposed neighbour
pair: either the inverse Henneberg 2 move is legal, or a concrete tight
blocking set containing that pair is returned.
-/
theorem legalInverseHennebergTwo_or_tightObstruction
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (habF : simpleEdge a b hab ∉ F) :
    LegalInverseHennebergTwo F X
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) ∨
      ∃ Y : Finset V,
        Y.Nonempty ∧ a ∈ Y ∧ b ∈ Y ∧ v ∉ Y ∧
          Tight22 (deleteVertexEdges F v) Y := by
  have hSparseDelete : Sparse22 (deleteVertexEdges F v) :=
    hG.sparse.mono (deleteVertexEdges_subset F v)
  by_cases hSparse :
      Sparse22 (insert (simpleEdge a b hab) (deleteVertexEdges F v))
  · exact Or.inl (legalInverseHennebergTwo_of_sparse_insert hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF hSparse)
  · exact Or.inr
      (exists_tight22_obstruction_of_not_hennebergTwo_admissible
        hva hab hSparseDelete habF hSparse)

/--
Nixon--Owen's degree-three admissibility argument in the branch where two
edges among the three neighbours already exist.  The third, missing edge
can always be inserted after deleting the degree-three vertex.
-/
theorem legalInverseHennebergTwo_of_other_two_neighbor_edges
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hacF : simpleEdge a c hac ∈ F)
    (hbcF : simpleEdge b c hbc ∈ F) :
    LegalInverseHennebergTwo F X
      (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) := by
  rcases legalInverseHennebergTwo_or_tightObstruction hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF with hLegal | hBlocked
  · exact hLegal
  · obtain ⟨Y, hYne, haY, hbY, hvY, hYtight⟩ := hBlocked
    have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
      hDegree hvaF hvbF hvcF
    have hcY : c ∉ Y := by
      intro hcY
      have hIncidentSupported :
          SupportedOn (incidentEdges F v) (insert v Y) := by
        intro e he
        rw [hIncidentEq] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · rw [vertices_simpleEdge]
          simp [haY]
        · rw [vertices_simpleEdge]
          simp [hbY]
        · rw [vertices_simpleEdge]
          simp [hcY]
      have hCard := card_edgesInside_insert_eq_degree_add F Y v hvY hIncidentSupported
      have hSparseZ := hG.sparse (insert v Y) ⟨v, by simp⟩
      have hZcard : (insert v Y).card = Y.card + 1 := by
        rw [Finset.card_insert_of_notMem hvY]
      rw [hCard, hDegree, hYtight.2, hZcard] at hSparseZ
      have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
      omega
    let eac : SimpleEdge V := simpleEdge a c hac
    let ebc : SimpleEdge V := simpleEdge b c hbc
    let R : SimpleEdgeSet V := deleteVertexEdges F v
    have eacR : eac ∈ R := by
      rw [mem_deleteVertexEdges]
      refine ⟨hacF, ?_⟩
      rw [vertices_simpleEdge]
      simp [hva, hvc]
    have ebcR : ebc ∈ R := by
      rw [mem_deleteVertexEdges]
      refine ⟨hbcF, ?_⟩
      rw [vertices_simpleEdge]
      simp [hvb, hvc]
    have eacNew : eac ∈ edgesInside R (insert c Y) := by
      rw [mem_edgesInside]
      refine ⟨eacR, ?_⟩
      rw [vertices_simpleEdge]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_insert_of_mem haY
      · exact Finset.mem_insert_self _ _
    have ebcNew : ebc ∈ edgesInside R (insert c Y) := by
      rw [mem_edgesInside]
      refine ⟨ebcR, ?_⟩
      rw [vertices_simpleEdge]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_insert_of_mem hbY
      · exact Finset.mem_insert_self _ _
    have hPairCard : ({eac, ebc} : SimpleEdgeSet V).card = 2 := by
      simp [eac, ebc, hab, hac]
    have hPairDisjoint :
        Disjoint (edgesInside R Y) ({eac, ebc} : SimpleEdgeSet V) := by
      rw [Finset.disjoint_left]
      intro e heOld hePair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
      rcases hePair with rfl | rfl
      · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [eac]))
      · exact hcY ((mem_edgesInside.mp heOld).2 (by simp [ebc]))
    have hUnionSubset :
        edgesInside R Y ∪ ({eac, ebc} : SimpleEdgeSet V) ⊆
          edgesInside R (insert c Y) := by
      intro e he
      rw [Finset.mem_union] at he
      rcases he with heOld | hePair
      · exact edgesInside_mono_vertices R (Finset.subset_insert c Y) heOld
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hePair
        rcases hePair with rfl | rfl
        · exact eacNew
        · exact ebcNew
    have hDeletedLower :
        (edgesInside R Y).card + 2 ≤
          (edgesInside R (insert c Y)).card := by
      rw [← hPairCard,
        ← Finset.card_union_of_disjoint hPairDisjoint]
      exact Finset.card_le_card hUnionSubset
    have hvInsertCY : v ∉ insert c Y := by
      simp [hvc, hvY]
    have hIncidentSupported :
        SupportedOn (incidentEdges F v) (insert v (insert c Y)) := by
      intro e he
      rw [hIncidentEq] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · rw [vertices_simpleEdge]
        simp [haY]
      · rw [vertices_simpleEdge]
        simp [hbY]
      · rw [vertices_simpleEdge]
        simp
    have hCard := card_edgesInside_insert_eq_degree_add
      F (insert c Y) v hvInsertCY hIncidentSupported
    have hSparseZ := hG.sparse (insert v (insert c Y)) ⟨v, by simp⟩
    have hCYcard : (insert c Y).card = Y.card + 1 := by
      rw [Finset.card_insert_of_notMem hcY]
    have hZcard : (insert v (insert c Y)).card = Y.card + 2 := by
      rw [Finset.card_insert_of_notMem hvInsertCY, hCYcard]
    rw [hCard, hDegree, hZcard] at hSparseZ
    dsimp [R] at hDeletedLower
    rw [hYtight.2] at hDeletedLower
    have hYpos : 0 < Y.card := Finset.card_pos.mpr hYne
    omega

/--
Nixon--Owen's second degree-three branch: if two consecutive neighbour
pairs are missing, at least one of the two corresponding inverse
Henneberg 2 moves is legal.  Two hypothetical blocking sets uncross along
their common neighbour; adjoining the deleted vertex to their tight union
then violates sparsity by one edge.
-/
theorem legalInverseHennebergTwo_of_two_missing_neighbor_edges
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F)
    (habF : simpleEdge a b hab ∉ F)
    (hbcF : simpleEdge b c hbc ∉ F) :
    LegalInverseHennebergTwo F X
        (insert (simpleEdge a b hab) (deleteVertexEdges F v)) (X.erase v) ∨
      LegalInverseHennebergTwo F X
        (insert (simpleEdge b c hbc) (deleteVertexEdges F v)) (X.erase v) := by
  rcases legalInverseHennebergTwo_or_tightObstruction hG hva hvb hab
      hvX haX hbX hDegree hvaF hvbF habF with hLegalAB | hBlockedAB
  · exact Or.inl hLegalAB
  rcases legalInverseHennebergTwo_or_tightObstruction hG hvb hvc hbc
      hvX hbX hcX hDegree hvbF hvcF hbcF with hLegalBC | hBlockedBC
  · exact Or.inr hLegalBC
  obtain ⟨Yab, _hYabNe, haYab, hbYab, hvYab, hYabTight⟩ := hBlockedAB
  obtain ⟨Ybc, _hYbcNe, hbYbc, hcYbc, hvYbc, hYbcTight⟩ := hBlockedBC
  let R : SimpleEdgeSet V := deleteVertexEdges F v
  have hSparseR : Sparse22 R :=
    hG.sparse.mono (deleteVertexEdges_subset F v)
  have hInterNonempty : (Yab ∩ Ybc).Nonempty :=
    ⟨b, Finset.mem_inter.mpr ⟨hbYab, hbYbc⟩⟩
  have hUnionTight : Tight22 R (Yab ∪ Ybc) :=
    (tight22_union_inter hSparseR hYabTight hYbcTight hInterNonempty).1
  have hvUnion : v ∉ Yab ∪ Ybc := by
    simp [hvYab, hvYbc]
  have hIncidentEq := incidentEdges_eq_three hva hvb hvc hab hac hbc
    hDegree hvaF hvbF hvcF
  have hIncidentSupported :
      SupportedOn (incidentEdges F v) (insert v (Yab ∪ Ybc)) := by
    intro e he
    rw [hIncidentEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [vertices_simpleEdge]
      simp [haYab]
    · rw [vertices_simpleEdge]
      simp [hbYab]
    · rw [vertices_simpleEdge]
      simp [hcYbc]
  have hCard := card_edgesInside_insert_eq_degree_add
    F (Yab ∪ Ybc) v hvUnion hIncidentSupported
  have hSparseZ := hG.sparse (insert v (Yab ∪ Ybc)) ⟨v, by simp⟩
  have hZcard :
      (insert v (Yab ∪ Ybc)).card = (Yab ∪ Ybc).card + 1 := by
    rw [Finset.card_insert_of_notMem hvUnion]
  rw [hCard, hDegree, hZcard] at hSparseZ
  have hUnionCount := hUnionTight.2
  dsimp [R] at hUnionCount
  rw [hUnionCount] at hSparseZ
  have hUnionPos : 0 < (Yab ∪ Ybc).card :=
    Finset.card_pos.mpr hUnionTight.1
  omega

/--
Formal Nixon--Owen Lemma 3.1 for three named neighbours: a degree-three
vertex is either contained in the `K₄` on those neighbours, or admits a
legal inverse Henneberg 2 move.  This theorem combines the one-missing and
two-missing obstruction arguments above.
-/
theorem named_degree_three_k4_or_legalInverseHennebergTwo
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvX : v ∈ X) (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hDegree : edgeSetDegree F v = 3)
    (hvaF : simpleEdge v a hva ∈ F)
    (hvbF : simpleEdge v b hvb ∈ F)
    (hvcF : simpleEdge v c hvc ∈ F) :
    NamedK4Witness F v a b c ∨
      ∃ F' : SimpleEdgeSet V,
        LegalInverseHennebergTwo F X F' (X.erase v) := by
  by_cases hAB : simpleEdge a b hab ∈ F
  · by_cases hAC : simpleEdge a c hac ∈ F
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · exact Or.inl ⟨hva, hvb, hvc, hab, hac, hbc,
          hvaF, hvbF, hvcF, hAB, hAC, hBC⟩
      · have hBA : simpleEdge b a (Ne.symm hab) ∈ F := by
          rw [← simpleEdge_comm a b hab]
          exact hAB
        have hCA : simpleEdge c a (Ne.symm hac) ∈ F := by
          rw [← simpleEdge_comm a c hac]
          exact hAC
        have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hvb hvc hva hbc (Ne.symm hab) (Ne.symm hac)
          hvX hbX hcX haX hDegree hvbF hvcF hvaF hBC hBA hCA
        exact Or.inr ⟨_, hLegal⟩
    · by_cases hBC : simpleEdge b c hbc ∈ F
      · have hCB : simpleEdge c b (Ne.symm hbc) ∈ F := by
          rw [← simpleEdge_comm b c hbc]
          exact hBC
        have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hva hvc hvb hac hab (Ne.symm hbc)
          hvX haX hcX hbX hDegree hvaF hvcF hvbF hAC hAB hCB
        exact Or.inr ⟨_, hLegal⟩
      · have hCB : simpleEdge c b (Ne.symm hbc) ∉ F := by
          rw [← simpleEdge_comm b c hbc]
          exact hBC
        rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
            hG hva hvc hvb hac hab (Ne.symm hbc)
            hvX haX hcX hbX hDegree hvaF hvcF hvbF hAC hCB with hLegal | hLegal
        · exact Or.inr ⟨_, hLegal⟩
        · exact Or.inr ⟨_, hLegal⟩
  · by_cases hBC : simpleEdge b c hbc ∈ F
    · by_cases hAC : simpleEdge a c hac ∈ F
      · have hLegal := legalInverseHennebergTwo_of_other_two_neighbor_edges
          hG hva hvb hvc hab hac hbc
          hvX haX hbX hcX hDegree hvaF hvbF hvcF hAB hAC hBC
        exact Or.inr ⟨_, hLegal⟩
      · have hCA : simpleEdge c a (Ne.symm hac) ∉ F := by
          rw [← simpleEdge_comm a c hac]
          exact hAC
        rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
            hG hvc hva hvb (Ne.symm hac) (Ne.symm hbc) hab
            hvX hcX haX hbX hDegree hvcF hvaF hvbF hCA hAB with hLegal | hLegal
        · exact Or.inr ⟨_, hLegal⟩
        · exact Or.inr ⟨_, hLegal⟩
    · rcases legalInverseHennebergTwo_of_two_missing_neighbor_edges
          hG hva hvb hvc hab hac hbc
          hvX haX hbX hcX hDegree hvaF hvbF hvcF hAB hBC with hLegal | hLegal
      · exact Or.inr ⟨_, hLegal⟩
      · exact Or.inr ⟨_, hLegal⟩

/-- Coordinate-free form of the preceding theorem for an arbitrary degree-three vertex. -/
theorem degree_three_k4_or_legalInverseHennebergTwo
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hvX : v ∈ X) (hDegree : edgeSetDegree F v = 3) :
    (∃ a b c : V, NamedK4Witness F v a b c) ∨
      ∃ F' : SimpleEdgeSet V,
        LegalInverseHennebergTwo F X F' (X.erase v) := by
  have hIncidentCard : (incidentEdges F v).card = 3 := hDegree
  obtain ⟨e₁, e₂, e₃, he₁₂, he₁₃, he₂₃, hIncidentEq⟩ :=
    Finset.card_eq_three.mp hIncidentCard
  have he₁Incident : e₁ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₂Incident : e₂ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  have he₃Incident : e₃ ∈ incidentEdges F v := by
    rw [hIncidentEq]
    simp
  obtain ⟨a, hva, he₁⟩ :=
    exists_otherEndpoint e₁ (mem_incidentEdges.mp he₁Incident).2
  obtain ⟨b, hvb, he₂⟩ :=
    exists_otherEndpoint e₂ (mem_incidentEdges.mp he₂Incident).2
  obtain ⟨c, hvc, he₃⟩ :=
    exists_otherEndpoint e₃ (mem_incidentEdges.mp he₃Incident).2
  have hab : a ≠ b := by
    intro hab
    subst b
    apply he₁₂
    calc
      e₁ = simpleEdge v a hva := he₁
      _ = simpleEdge v a hvb := by rfl
      _ = e₂ := he₂.symm
  have hac : a ≠ c := by
    intro hac
    subst c
    apply he₁₃
    calc
      e₁ = simpleEdge v a hva := he₁
      _ = simpleEdge v a hvc := by rfl
      _ = e₃ := he₃.symm
  have hbc : b ≠ c := by
    intro hbc
    subst c
    apply he₂₃
    calc
      e₂ = simpleEdge v b hvb := he₂
      _ = simpleEdge v b hvc := by rfl
      _ = e₃ := he₃.symm
  have hvaF : simpleEdge v a hva ∈ F := by
    rw [← he₁]
    exact (mem_incidentEdges.mp he₁Incident).1
  have hvbF : simpleEdge v b hvb ∈ F := by
    rw [← he₂]
    exact (mem_incidentEdges.mp he₂Incident).1
  have hvcF : simpleEdge v c hvc ∈ F := by
    rw [← he₃]
    exact (mem_incidentEdges.mp he₃Incident).1
  have haX : a ∈ X := hG.supported hvaF (by simp)
  have hbX : b ∈ X := hG.supported hvbF (by simp)
  have hcX : c ∈ X := hG.supported hvcF (by simp)
  rcases named_degree_three_k4_or_legalInverseHennebergTwo
      hG hva hvb hvc hab hac hbc hvX haX hbX hcX
      hDegree hvaF hvbF hvcF with hK4 | hLegal
  · exact Or.inl ⟨a, b, c, hK4⟩
  · exact Or.inr hLegal

/-- A degree-two vertex supplies the first disjunct of the full reduction theorem. -/
theorem hasNixonOwenReduction_of_degree_two
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    {v : V} (hv : v ∈ X) (hDegree : edgeSetDegree F v = 2) :
    HasNixonOwenReduction F X := by
  refine ⟨deleteVertexEdges F v, X.erase v, ?_, Or.inl ?_⟩
  · rw [Finset.card_erase_of_mem hv]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide)
  · exact legalInverseHennebergOne_of_degree_two hG hv hDegree

/-- The elementary counting step in Nixon--Owen Lemma 3.2: either inverse
Henneberg 1 applies, or the graph has a vertex of degree three. -/
theorem hasNixonOwenReduction_or_exists_degree_three
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨
      ∃ v ∈ X, edgeSetDegree F v = 3 := by
  obtain ⟨v, hv, hDegree | hDegree⟩ :=
    exists_edgeSetDegree_eq_two_or_three hG hXcard
  · exact Or.inl (hasNixonOwenReduction_of_degree_two hG hv hDegree)
  · exact Or.inr ⟨v, hv, hDegree⟩

/--
Closed low-degree boundary of Nixon--Owen Lemmas 3.1--3.2: every supported
`(2,2)`-tight graph with at least two vertices either already has one of
the four legal reductions (in fact Henneberg 1 or 2 at this stage), or a
degree-three vertex is certified inside a named `K₄`.
-/
theorem hasNixonOwenReduction_or_degree_three_in_K4
    {F : SimpleEdgeSet V} {X : Finset V} (hG : SimpleTight22On F X)
    (hXcard : 2 ≤ X.card) :
    HasNixonOwenReduction F X ∨
      ∃ v ∈ X, ∃ a b c : V, NamedK4Witness F v a b c := by
  obtain ⟨v, hv, hDegree | hDegree⟩ :=
    exists_edgeSetDegree_eq_two_or_three hG hXcard
  · exact Or.inl (hasNixonOwenReduction_of_degree_two hG hv hDegree)
  · rcases degree_three_k4_or_legalInverseHennebergTwo hG hv hDegree with
      hK4 | ⟨F', hLegal⟩
    · exact Or.inr ⟨v, hv, hK4⟩
    · refine Or.inl ⟨F', X.erase v, hLegal.1.card_lt, ?_⟩
      exact Or.inr (Or.inl hLegal)

end RB31E2E
