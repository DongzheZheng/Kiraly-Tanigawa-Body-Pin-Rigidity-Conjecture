import RB31EndToEnd.Specification
import RB31EndToEnd.Graph.LooplessMultiGraph
import RB31EndToEnd.Rigidity.BarJoint

/-!
# The body--pin graph as a union of body cliques

Every pin occurrence is one shared graph vertex.  Independently, each body has
four distinguished private vertices and may have any prescribed number of
additional private vertices.  The bars are exactly the pairs lying in a common
body, so the resulting simple graph is literally a supremum of cliques.
-/

namespace RB31E2E

namespace BodyPinIncidence

/-- Forget only multiplicity aggregation: every pin remains an edge occurrence. -/
def toLooplessMultiGraph (H : BodyPinIncidence) : LooplessMultiGraph where
  Vertex := H.Body
  Edge := H.Pin
  vertexFinite := H.bodyFinite
  edgeFinite := H.pinFinite
  vertexDecidableEq := H.bodyDecidableEq
  edgeDecidableEq := H.pinDecidableEq
  source := H.left
  target := H.right
  loopless := H.loopless

@[simp] theorem toLooplessMultiGraph_source (H : BodyPinIncidence) (e : H.Pin) :
    H.toLooplessMultiGraph.source e = H.left e :=
  rfl

@[simp] theorem toLooplessMultiGraph_target (H : BodyPinIncidence) (e : H.Pin) :
    H.toLooplessMultiGraph.target e = H.right e :=
  rfl

/--
Vertices of the expanded bar--joint graph: shared pin occurrences on the left,
and body-labelled private vertices on the right.  `extra b` can enlarge body
`b`, while `4 + extra b` guarantees a private tetrahedral core.
-/
abbrev BPVertex (H : BodyPinIncidence) (extra : H.Body → ℕ) :=
  H.Pin ⊕ ((b : H.Body) × Fin (4 + extra b))

/-- The graph vertex belonging to a pin occurrence. -/
def pinVertex (H : BodyPinIncidence) (extra : H.Body → ℕ) (e : H.Pin) :
    H.BPVertex extra :=
  Sum.inl e

/-- A private graph vertex belonging only to `b`. -/
def privateVertex (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) (i : Fin (4 + extra b)) : H.BPVertex extra :=
  Sum.inr ⟨b, i⟩

/-- Incidence of an expanded graph vertex with a body clique. -/
def VertexBelongsToBody (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) : H.BPVertex extra → Prop
  | Sum.inl e => H.left e = b ∨ H.right e = b
  | Sum.inr x => x.1 = b

@[simp] theorem pinVertex_belongs_iff (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (b : H.Body) (e : H.Pin) :
    H.VertexBelongsToBody extra b (H.pinVertex extra e) ↔
      H.left e = b ∨ H.right e = b :=
  Iff.rfl

@[simp] theorem privateVertex_belongs_iff (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (b c : H.Body) (i : Fin (4 + extra c)) :
    H.VertexBelongsToBody extra b (H.privateVertex extra c i) ↔ c = b :=
  Iff.rfl

/-- The complete simple graph supported on the vertices belonging to one body. -/
def bodyClique (H : BodyPinIncidence) (extra : H.Body → ℕ) (b : H.Body) :
    SimpleGraph (H.BPVertex extra) where
  Adj v w := v ≠ w ∧
    H.VertexBelongsToBody extra b v ∧ H.VertexBelongsToBody extra b w
  symm v w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

theorem bodyClique_isClique (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) :
    (H.bodyClique extra b).IsClique
      {v | H.VertexBelongsToBody extra b v} := by
  rw [SimpleGraph.isClique_iff]
  intro v hv w hw hvw
  change v ≠ w ∧
    H.VertexBelongsToBody extra b v ∧ H.VertexBelongsToBody extra b w
  exact ⟨hvw, hv, hw⟩

/-- The expanded body--pin graph, definitionally the union of its body cliques. -/
def bodyPinGraph (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    SimpleGraph (H.BPVertex extra) :=
  ⨆ b : H.Body, H.bodyClique extra b

theorem bodyPinGraph_eq_iSup_bodyClique
    (H : BodyPinIncidence) (extra : H.Body → ℕ) :
    H.bodyPinGraph extra = ⨆ b : H.Body, H.bodyClique extra b :=
  rfl

theorem bodyPinGraph_adj_iff (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (v w : H.BPVertex extra) :
    (H.bodyPinGraph extra).Adj v w ↔
      ∃ b : H.Body, v ≠ w ∧
        H.VertexBelongsToBody extra b v ∧
        H.VertexBelongsToBody extra b w := by
  simp [bodyPinGraph, SimpleGraph.iSup_adj, bodyClique]

/-- The `i`th of four canonical private vertices in body `b`. -/
def privateCoreVertex (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) (i : Fin 4) : H.BPVertex extra :=
  H.privateVertex extra b (Fin.castLE (Nat.le_add_right 4 (extra b)) i)

theorem privateCoreVertex_injective (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (b : H.Body) :
    Function.Injective (H.privateCoreVertex extra b) := by
  intro i j hij
  have hval : i.val = j.val := by
    simpa [privateCoreVertex, privateVertex] using
      congrArg
        (fun v : H.BPVertex extra ↦
          match v with
          | Sum.inl _ => 0
          | Sum.inr x => x.2.val)
        hij
  exact Fin.ext hval

theorem privateCoreVertex_belongs (H : BodyPinIncidence)
    (extra : H.Body → ℕ) (b : H.Body) (i : Fin 4) :
    H.VertexBelongsToBody extra b (H.privateCoreVertex extra b i) := by
  rfl

/-- Each body contains a canonical `K₄`, independent of its pin degree. -/
theorem privateCore_adj (H : BodyPinIncidence) (extra : H.Body → ℕ)
    (b : H.Body) {i j : Fin 4} (hij : i ≠ j) :
    (H.bodyPinGraph extra).Adj
      (H.privateCoreVertex extra b i) (H.privateCoreVertex extra b j) := by
  rw [H.bodyPinGraph_adj_iff extra]
  refine ⟨b, ?_, H.privateCoreVertex_belongs extra b i,
    H.privateCoreVertex_belongs extra b j⟩
  exact fun h => hij (H.privateCoreVertex_injective extra b h)

/-- The canonical expansion with exactly four private vertices per body. -/
def canonicalBodyPinGraph (H : BodyPinIncidence) :
    SimpleGraph (H.BPVertex fun _ ↦ 0) :=
  H.bodyPinGraph fun _ ↦ 0

/-- Real maximum-rank generic rigidity of the actual expanded graph. -/
def GenericallyRigidInR3 (H : BodyPinIncidence) (extra : H.Body → ℕ) : Prop :=
  BarJoint.IsGenericallyRigidInR3 (H.bodyPinGraph extra)

/-- Generic rigidity of the canonical four-private-vertices expansion. -/
def CanonicallyGenericallyRigidInR3 (H : BodyPinIncidence) : Prop :=
  H.GenericallyRigidInR3 fun _ ↦ 0

end BodyPinIncidence

end RB31E2E
