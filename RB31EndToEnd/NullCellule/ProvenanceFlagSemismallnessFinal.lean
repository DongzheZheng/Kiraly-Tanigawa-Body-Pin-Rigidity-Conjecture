import RB31EndToEnd.NullCellule.ProvenanceFlagOutsideExceptional
import RB31EndToEnd.NullCellule.ProvenanceFlagPrivateExceptional

/-!
# Provenance-flag semismallness

Strong induction on the number of live vertices combines the outside and
private exceptional steps with the nonexceptional recursion.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

open DirectionStress

universe u v w x

variable {k : Type u} {K : Type v} {V : Type w} {Flag : Type x}
  [Field k] [Field K] [Algebra k K]
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- The exact smaller-state induction resource. -/
private abbrev SmallerSemismallFinal
    (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ {K : Type v} {V : Type w} {Flag : Type x}
    [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
    Fintype.card V < n →
      ∀ (S : State V Flag)
        (Y : FunctionFieldBranch (k := k) (K := K) S),
        S.CompletionSparse → Y.SemismallBudget S

/-- **Provenance-flag semismallness.**  For every literal flagged state
whose private-ghost completion is `(2,2)`-sparse, every coordinate-generated
injective function-field branch satisfies the stress/codimension budget.

The structures `State` and `FunctionFieldBranch` contain no semismallness or
height conclusion. -/
theorem provenanceFlag_semismallness
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (Y : FunctionFieldBranch (k := k) (K := K) S) :
    Y.SemismallBudget S := by
  let P : ℕ → Prop := fun n ↦
    ∀ {K : Type v} {V : Type w} {Flag : Type x}
      [Field K] [Algebra k K]
      [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag],
      Fintype.card V = n →
        ∀ (S : State V Flag)
          (Y : FunctionFieldBranch (k := k) (K := K) S),
          S.CompletionSparse → Y.SemismallBudget S
  have hAll : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro K' V' Flag' _instField _instAlgebra
          _instFintypeV _instDecidableV _instFintypeFlag _instDecidableFlag
          hCard S' Y' hSparse'
        have hSmaller :
            SmallerSemismallFinal.{u, v, w, x}
              (k := k) (Fintype.card V') := by
          intro K'' V'' Flag'' _instField'' _instAlgebra''
            _instFintypeV'' _instDecidableV''
            _instFintypeFlag'' _instDecidableFlag''
            hCardLt S'' Y'' hSparse''
          exact ih (Fintype.card V'') (by omega) rfl S'' Y'' hSparse''
        by_cases hZero : Fintype.card V' = 0
        · exact Y'.semismallBudget_of_card_live_eq_zero S' hZero
        have hVPos : 0 < Fintype.card V' := Nat.pos_of_ne_zero hZero
        obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hVPos
        have hUniverse : (Finset.univ : Finset V').Nonempty :=
          ⟨v₀, Finset.mem_univ v₀⟩
        rcases S'.exists_outside_degree_le_three_or_private_degree_le_two
            hSparse' hUniverse with hOutside | hPrivate
        · obtain ⟨v₀, hvOutside, hDegree⟩ := hOutside
          rcases outside_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · have hChildCard :
                Fintype.card (RemainingVertex v₀) < n := by
              have hDrop := card_remainingVertex_add_one v₀
              omega
            have hChild :
                (Y'.deleteOutsideIntrinsic S' v₀ hvOutside).SemismallBudget
                  (S'.deleteOutside v₀ hvOutside) := by
              exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
                (S'.deleteOutside v₀ hvOutside)
                (Y'.deleteOutsideIntrinsic S' v₀ hvOutside)
                (S'.deleteOutside_completionSparse
                  v₀ hvOutside hSparse')
            exact Y'.semismallBudget_of_deleteOutsideIntrinsic
              S' v₀ hvOutside hChild hPaid
          · exact Y'.semismallBudget_of_outsideExceptional
              S' v₀ hSparse' hvOutside hDegree hSmaller hExceptional
        · obtain ⟨v₀, hvPrivate, hDegree⟩ := hPrivate
          have hActive : (S'.activeFlagsAt v₀).Nonempty := by
            apply Finset.card_pos.mp
            change 0 < S'.flagMultiplicity v₀
            omega
          obtain ⟨t₀, ht₀⟩ := hActive
          have hvt : v₀ ∈ S'.terminals t₀ :=
            (S'.mem_activeFlagsAt v₀ t₀).1 ht₀
          rcases private_nonexceptional_or_exceptional
              (k := k) S'.edges Y'.position v₀ with hPaid | hExceptional
          · have hChildCard :
                Fintype.card (RemainingVertex v₀) < n := by
              have hDrop := card_remainingVertex_add_one v₀
              omega
            have hChild :
                (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt).SemismallBudget
                  (S'.deletePrivate v₀ t₀ hvPrivate hvt) := by
              exact ih (Fintype.card (RemainingVertex v₀)) hChildCard rfl
                (S'.deletePrivate v₀ t₀ hvPrivate hvt)
                (Y'.deletePrivateIntrinsic S' v₀ t₀ hvPrivate hvt)
                (S'.deletePrivate_completionSparse
                  v₀ t₀ hvPrivate hvt hSparse')
            exact Y'.semismallBudget_of_deletePrivateIntrinsic
              S' v₀ t₀ hvPrivate hvt hChild hPaid
          · exact Y'.semismallBudget_of_privateExceptional
              S' v₀ t₀ hSparse' hvPrivate hvt hDegree
              hSmaller hExceptional
  exact hAll (Fintype.card V) rfl S Y hSparse

end ProvenanceFlag

end

end RB31E2E
