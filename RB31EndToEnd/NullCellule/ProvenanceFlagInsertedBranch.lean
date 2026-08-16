import RB31EndToEnd.NullCellule.ProvenanceFlagBranch
import RB31EndToEnd.Combinatorics.ProvenanceFlagInsertion

/-!
# Function-field branches after inserting one virtual live edge

Insertion changes only the live edge set.  The coordinate field, placement,
distinctness, active flags, terminal sets, and their collinearities remain
literal copies.  This small constructor lets both exceptional induction
moves apply the recursive semismallness theorem to an actually inserted
child state.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {k K V Flag : Type*}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Reinterpret a function-field branch on the state obtained by inserting
one certified live edge. -/
def FunctionFieldBranch.insertLiveEdge
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    FunctionFieldBranch (k := k) (K := K) (S.insertLiveEdge e heMissing) where
  position := Y.position
  generated := Y.generated
  distinct := Y.distinct
  collinear t := by
    simpa only [State.insertLiveEdge_terminals] using Y.collinear t

@[simp]
theorem FunctionFieldBranch.insertLiveEdge_position
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (Y.insertLiveEdge S e heMissing).position = Y.position := rfl

/-- Its stress dimension is the literal stress dimension of the inserted
edge set at the unchanged placement. -/
theorem FunctionFieldBranch.insertLiveEdge_stressDim
    (S : State V Flag)
    (Y : FunctionFieldBranch (k := k) (K := K) S)
    (e : SimpleEdge V) (heMissing : ∀ t : Flag, e ≠ S.missing t) :
    (Y.insertLiveEdge S e heMissing).stressDim
        (S.insertLiveEdge e heMissing) =
      DirectionStress.directionStressDim (insert e S.edges) Y.position := rfl

end ProvenanceFlag

end

end RB31E2E
