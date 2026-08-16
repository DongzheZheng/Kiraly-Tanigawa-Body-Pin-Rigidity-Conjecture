import RB31EndToEnd.NullCellule.ProvenanceFlagSemismallness
import RB31EndToEnd.Combinatorics.ProvenanceFlagOutsideRegistration

/-!
# The intrinsic function-field branch after outside registration

The complete exceptional outside move deletes the degree-three apex and
registers its three retained neighbours as one new active flag.  This file
constructs the literal function-field branch on that registered state.  Old
flag collinearities are inherited from outside deletion; the new one is
proved by descending the actual neighbour collinearity to the field generated
by the retained coordinates.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
/-- A collinear triple of pairwise distinct points is an affine-collinear
three-element set.  This is the small conversion used for the newly
registered flag. -/
theorem affinelyCollinearOn_three_of_collinear
    {W : Type*} [DecidableEq W]
    (a : W → Fin 3 → K) (p q r : W)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpos : a p ≠ a q)
    (hcol : PinCollinearity.Collinear (a p) (a q) (a r)) :
    AffinelyCollinearOn a ({p, q, r} : Finset W) := by
  obtain ⟨t, ht⟩ :=
    (collinear_iff_exists_smul_difference (a p) (a q) (a r) hpos).1 hcol
  refine ⟨a p, a q - a p, ?_⟩
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by module⟩
  · refine ⟨t, ?_⟩
    funext j
    have hj := congrFun ht j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linear_combination hj

/-- The genuine intrinsic branch on the state obtained by registering a
complete outside neighbour triangle. -/
def FunctionFieldBranch.registerOutsideIntrinsic
    (S : State V Flag) (Y : FunctionFieldBranch (k := k) (K := K) S)
    (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges)
    (hcol : PinCollinearity.Collinear
      (Y.position N.p) (Y.position N.q) (Y.position N.r)) :
    FunctionFieldBranch
      (k := k) (K := retainedLiveCoordinateField (k := k) Y.position v)
      (S.registerOutside hSparse v hvOutside N hTriangleLive) where
  position := intrinsicRestrictedPlacement (k := k) Y.position v
  generated := intrinsicRestrictedPlacement_generated (k := k) Y.position v
  distinct := by
    intro a b hab
    apply Subtype.ext
    apply Y.distinct
    funext j
    exact congrArg Subtype.val (congrFun hab j)
  collinear t := by
    cases t with
    | inl t =>
        exact (Y.deleteOutsideIntrinsic S v hvOutside).collinear t
    | inr t =>
        cases t
        let L := retainedLiveCoordinateField (k := k) Y.position v
        let childPosition := intrinsicRestrictedPlacement (k := k) Y.position v
        let p : RemainingVertex v := ⟨N.p, N.hvp.symm⟩
        let q : RemainingVertex v := ⟨N.q, N.hvq.symm⟩
        let r : RemainingVertex v := ⟨N.r, N.hvr.symm⟩
        have hpqChild : p ≠ q := by
          intro h
          exact N.hpq (congrArg Subtype.val h)
        have hprChild : p ≠ r := by
          intro h
          exact N.hpr (congrArg Subtype.val h)
        have hqrChild : q ≠ r := by
          intro h
          exact N.hqr (congrArg Subtype.val h)
        have hpqPosition : childPosition p ≠ childPosition q := by
          intro h
          exact hpqChild ((show Function.Injective childPosition from by
            intro a b hab
            apply Subtype.ext
            apply Y.distinct
            funext j
            exact congrArg Subtype.val (congrFun hab j)) h)
        have hcolL : PinCollinearity.Collinear
            (childPosition p) (childPosition q) (childPosition r) := by
          apply collinear_restrictScalars
            (k := k) (K := K) L
            (childPosition p) (childPosition q) (childPosition r)
            hpqPosition
          simpa [childPosition, intrinsicRestrictedPlacement, p, q, r] using hcol
        change AffinelyCollinearOn childPosition ({p, q, r} :
          Finset (RemainingVertex v))
        exact affinelyCollinearOn_three_of_collinear
          childPosition p q r hpqChild hprChild hqrChild hpqPosition hcolL

end ProvenanceFlag

end

end RB31E2E
