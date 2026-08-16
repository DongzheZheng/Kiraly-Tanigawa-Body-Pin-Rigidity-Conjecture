import RB31EndToEnd.Combinatorics.Sparse22.Basic

/-!
# Transport of `(2,2)`-sparsity along injective vertex maps

Deletion and flag registration change the literal live-vertex type.  This
file supplies the provenance-preserving transport lemma needed for those
steps: if every transported child edge is an edge of a sparse parent, then
the child edge set is sparse.  No graph-isomorphism or sparsity conclusion
is stored as data.
-/

namespace RB31E2E

namespace Sparse22Transport

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Map a simple edge along an injective map of vertices. -/
def mapSimpleEdge (f : V ↪ W) (e : SimpleEdge V) : SimpleEdge W :=
  ⟨e.1.map f, by
    rw [Sym2.isDiag_map f.injective]
    exact e.2⟩

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem mapSimpleEdge_val (f : V ↪ W) (e : SimpleEdge V) :
    (mapSimpleEdge f e).1 = e.1.map f := rfl

omit [DecidableEq V] [DecidableEq W] in
theorem mapSimpleEdge_injective (f : V ↪ W) :
    Function.Injective (mapSimpleEdge f) := by
  intro e g heg
  apply Subtype.ext
  exact Sym2.map.injective f.injective (Subtype.mk.inj heg)

/-- The induced embedding on simple edges. -/
def mapSimpleEdgeEmbedding (f : V ↪ W) : SimpleEdge V ↪ SimpleEdge W where
  toFun := mapSimpleEdge f
  inj' := mapSimpleEdge_injective f

/-- Map a finite simple edge set along an injective vertex map. -/
def mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V) : SimpleEdgeSet W :=
  F.map (mapSimpleEdgeEmbedding f)

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem mem_mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V)
    (e : SimpleEdge V) :
    mapSimpleEdge f e ∈ mapEdgeSet f F ↔ e ∈ F := by
  constructor
  · intro he
    obtain ⟨g, hg, hge⟩ := Finset.mem_map.mp he
    have : g = e := mapSimpleEdge_injective f hge
    simpa [this] using hg
  · intro he
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩

omit [DecidableEq V] [DecidableEq W] in
@[simp]
theorem card_mapEdgeSet (f : V ↪ W) (F : SimpleEdgeSet V) :
    (mapEdgeSet f F).card = F.card := by
  simp [mapEdgeSet]

/-- Mapping an edge along an embedding maps its two endpoints into the
mapped endpoint set. -/
theorem mapSimpleEdge_vertices_subset
    (f : V ↪ W) (e : SimpleEdge V) (X : Finset V)
    (heX : e.vertices ⊆ X) :
    (mapSimpleEdge f e).vertices ⊆ X.map f := by
  intro y hy
  have hymem : y ∈ e.1.map f := by
    simpa [SimpleEdge.vertices] using hy
  obtain ⟨x, hx, hxy⟩ := (Sym2.mem_map.mp hymem)
  have hxVertices : x ∈ e.vertices := by
    simpa [SimpleEdge.vertices] using hx
  exact Finset.mem_map.mpr ⟨x, heX hxVertices, hxy⟩

/-- The mapped induced child edges inject into the induced parent edges. -/
theorem map_edgesInside_subset_edgesInside
    (f : V ↪ W) (F : SimpleEdgeSet V) (H : SimpleEdgeSet W)
    (hFH : mapEdgeSet f F ⊆ H) (X : Finset V) :
    mapEdgeSet f (edgesInside F X) ⊆ edgesInside H (X.map f) := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  have hgData := mem_edgesInside.mp hg
  apply mem_edgesInside.mpr
  exact ⟨hFH ((mem_mapEdgeSet f F g).2 hgData.1),
    mapSimpleEdge_vertices_subset f g X hgData.2⟩

/-- If the transported child edges lie in a sparse parent edge set, then
the child itself is sparse. -/
theorem sparse22_of_mapEdgeSet_subset
    (f : V ↪ W) {F : SimpleEdgeSet V} {H : SimpleEdgeSet W}
    (hH : Sparse22 H) (hFH : mapEdgeSet f F ⊆ H) : Sparse22 F := by
  intro X hX
  have hMapCard :
      (edgesInside F X).card =
        (mapEdgeSet f (edgesInside F X)).card := by
    rw [card_mapEdgeSet]
  have hSubset := map_edgesInside_subset_edgesInside f F H hFH X
  have hCardLe := Finset.card_le_card hSubset
  have hMapX : (X.map f).Nonempty := Finset.Nonempty.map hX
  have hSparse := hH (X.map f) hMapX
  have hXCard : (X.map f).card = X.card := Finset.card_map _
  rw [← hMapCard] at hCardLe
  exact hCardLe.trans (by simpa [hXCard] using hSparse)

end

end Sparse22Transport

end RB31E2E
