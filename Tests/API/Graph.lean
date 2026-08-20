import RB31EndToEnd.API.Graph

/-! A consumer of the public graph facade and no other project facade. -/

namespace PublicAPISmoke.Graph

def makeLooplessMultiGraph
    (Vertex Edge : Type)
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (source target : Edge → Vertex)
    (loopless : ∀ e, source e ≠ target e) :
    RB31E2E.LooplessMultiGraph where
  Vertex := Vertex
  Edge := Edge
  vertexFinite := inferInstance
  edgeFinite := inferInstance
  vertexDecidableEq := inferInstance
  edgeDecidableEq := inferInstance
  source := source
  target := target
  loopless := loopless

example
    (Vertex Edge : Type)
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (source target : Edge → Vertex)
    (loopless : ∀ e, source e ≠ target e)
    (e : Edge) :
    (makeLooplessMultiGraph Vertex Edge source target loopless).source e = source e :=
  rfl

example (G : RB31E2E.LooplessMultiGraph) (v w : G.Vertex) :
    G.multiplicity v w = G.multiplicity w v :=
  G.multiplicity_comm v w

def hasEndpoints (G : RB31E2E.LooplessMultiGraph)
    (e : G.Edge) (v w : G.Vertex) : Prop :=
  G.HasEndpoints e v w

noncomputable def edgesBetween (G : RB31E2E.LooplessMultiGraph)
    (v w : G.Vertex) : Finset G.Edge :=
  G.edgesBetween v w

noncomputable def multiplicity (G : RB31E2E.LooplessMultiGraph)
    (v w : G.Vertex) : ℕ :=
  G.multiplicity v w

def underlyingSimpleGraph (G : RB31E2E.LooplessMultiGraph) :
    SimpleGraph G.Vertex :=
  G.underlyingSimpleGraph

example (G : RB31E2E.LooplessMultiGraph)
    (e : G.Edge) (v w : G.Vertex) :
    G.HasEndpoints e v w ↔ G.HasEndpoints e w v :=
  G.hasEndpoints_comm e v w

example (G : RB31E2E.LooplessMultiGraph) (v w : G.Vertex) :
    G.edgesBetween v w = G.edgesBetween w v :=
  G.edgesBetween_comm v w

example (G : RB31E2E.LooplessMultiGraph)
    (e : G.Edge) (v : G.Vertex) :
    ¬ G.HasEndpoints e v v :=
  G.no_edge_has_equal_endpoints e v

example (G : RB31E2E.LooplessMultiGraph) (v : G.Vertex) :
    G.edgesBetween v v = ∅ :=
  G.edgesBetween_self v

example (G : RB31E2E.LooplessMultiGraph) (v : G.Vertex) :
    G.multiplicity v v = 0 :=
  G.multiplicity_self v

example (G : RB31E2E.LooplessMultiGraph) (v w : G.Vertex) :
    G.underlyingSimpleGraph.Adj v w ↔
      ∃ e, G.HasEndpoints e v w :=
  G.underlyingSimpleGraph_adj_iff v w

example (G : RB31E2E.LooplessMultiGraph) (v w : G.Vertex) :
    G.underlyingSimpleGraph.Adj v w ↔
      0 < G.multiplicity v w :=
  G.underlyingSimpleGraph_adj_iff_multiplicity_pos v w

end PublicAPISmoke.Graph
