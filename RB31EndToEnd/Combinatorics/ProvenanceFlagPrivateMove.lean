import RB31EndToEnd.Combinatorics.ProvenanceFlagPrivateDeletion
import RB31EndToEnd.Combinatorics.ProvenanceFlagOutsideMove
import RB31EndToEnd.Combinatorics.ProvenanceFlagForest

/-!
# The private exceptional augmentation move

In a pivoted private
flag `T = {v,p,q}` the distinguished missing edge is `vq`, while `vp` and
`pq` are live.  If the degree-two star has second endpoint `z`, then after
deleting `v` and the consumed ghost `T`, at least one of `pz,qz` is a
genuinely absent edge whose insertion preserves completion sparsity.

The obstruction proof uses the literal tight completed `K₄` of the old
flag.  A blocking tight set containing `p,q` would uncross with this `K₄`
to a two-vertex tight set, impossible in a simple `(2,2)`-sparse graph.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

private theorem two_le_card_of_pair_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f : SimpleEdge W} (hef : e ≠ f)
    (hsub : ({e, f} : SimpleEdgeSet W) ⊆ F) :
    2 ≤ F.card := by
  have hcard : ({e, f} : SimpleEdgeSet W).card = 2 := by simp [hef]
  rw [← hcard]
  exact Finset.card_le_card hsub

private theorem three_le_card_of_triple_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f g : SimpleEdge W}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hsub : ({e, f, g} : SimpleEdgeSet W) ⊆ F) :
    3 ≤ F.card := by
  have hcard : ({e, f, g} : SimpleEdgeSet W).card = 3 := by
    simp [hef, heg, hfg]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- No tight set in the double-deleted completion can contain both retained
endpoints of the consumed pivoted flag. -/
private theorem State.no_tightSet_in_privateDoubleDelete_containing_endpoints
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q : V) (t : Flag)
    (hvp : v ≠ p) (_hvq : v ≠ q) (hpq : p ≠ q)
    (hTerminals : S.terminals t = {v, p, q})
    (U : Finset (V ⊕ Flag))
    (hU : Tight22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)) U)
    (hpU : Sum.inl p ∈ U) (hqU : Sum.inl q ∈ U) :
    False := by
  let Q := deleteVertexEdges
    (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)
  have hQSub : Q ⊆ S.completionEdges :=
    (deleteVertexEdges_subset _ _).trans (deleteVertexEdges_subset _ _)
  have hQSparse : Sparse22 Q := hSparse.mono hQSub
  have hvU : Sum.inl v ∉ U := by
    exact not_mem_of_tight22_deleteVertexEdges hQSparse hU hpU
      (by simpa using hvp)
  have hDeleteComm : Q =
      deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t) := by
    ext e
    simp only [Q, mem_deleteVertexEdges]
    tauto
  have hQSparseComm : Sparse22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t)) := by
    rw [← hDeleteComm]
    exact hQSparse
  have hUComm : Tight22
      (deleteVertexEdges
        (deleteVertexEdges S.completionEdges (Sum.inl v)) (Sum.inr t)) U := by
    rw [← hDeleteComm]
    exact hU
  have htU : Sum.inr t ∉ U := by
    exact not_mem_of_tight22_deleteVertexEdges hQSparseComm hUComm hpU (by simp)
  have hInsideSub :
      edgesInside Q U ⊆ edgesInside S.completionEdges U :=
    edgesInside_mono_edges hQSub U
  have hLower := Finset.card_le_card hInsideSub
  have hUpper := hSparse U hU.1
  have hParentTight : Tight22 S.completionEdges U := by
    refine ⟨hU.1, ?_⟩
    rw [hU.2] at hLower
    omega
  let Kt := S.flagVertices t
  have hInterEq : U ∩ Kt = {Sum.inl p, Sum.inl q} := by
    ext x
    constructor
    · intro hx
      have hxU := (Finset.mem_inter.mp hx).1
      have hxK := (Finset.mem_inter.mp hx).2
      cases x with
      | inl a =>
          have haT : a ∈ S.terminals t :=
            (S.mem_flagVertices_live t a).1 hxK
          rw [hTerminals] at haT
          simp only [Finset.mem_insert, Finset.mem_singleton] at haT
          rcases haT with hav | hap | haq
          · subst a
            exact (hvU hxU).elim
          · apply Finset.mem_insert.mpr
            exact Or.inl (congrArg Sum.inl hap)
          · apply Finset.mem_insert.mpr
            exact Or.inr (Finset.mem_singleton.mpr (congrArg Sum.inl haq))
      | inr u =>
          have hut : u = t := (S.mem_flagVertices_ghost t u).1 hxK
          subst u
          exact (htU hxU).elim
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxp | hxq
      · subst x
        exact Finset.mem_inter.mpr
          ⟨hpU, (S.mem_flagVertices_live t p).2 (by rw [hTerminals]; simp)⟩
      · subst x
        exact Finset.mem_inter.mpr
          ⟨hqU, (S.mem_flagVertices_live t q).2 (by rw [hTerminals]; simp)⟩
  have hInterNonempty : (U ∩ Kt).Nonempty :=
    ⟨Sum.inl p, Finset.mem_inter.mpr
      ⟨hpU, (S.mem_flagVertices_live t p).2 (by rw [hTerminals]; simp)⟩⟩
  have hInterTight :=
    (tight22_union_inter hSparse hParentTight
      (S.flagVertices_tight hSparse t) hInterNonempty).2
  have hInterTwo : 2 ≤ (U ∩ Kt).card := by
    rw [hInterEq]
    simp [hpq]
  have hFour := four_le_card_of_tight22 hInterTight hInterTwo
  rw [hInterEq] at hFour
  simp [hpq] at hFour

/-- In the pivoted private degree-two shape, one of the two
virtual response edges is genuinely addable to the completed child after
the private terminal and its unique ghost are consumed. -/
theorem State.private_response_edge_addable
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v p q z : V) (t : Flag)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvz : v ≠ z)
    (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z)
    (hTerminals : S.terminals t = {v, p, q})
    (hpqLive : simpleEdge p q hpq ∈ S.edges)
    (hvzLive : simpleEdge v z hvz ∈ S.edges) :
    ∃ f : SimpleEdge V,
      (f = simpleEdge p z hpz ∨ f = simpleEdge q z hqz) ∧
      liftLiveEdge (Flag := Flag) f ∉ S.completionEdges ∧
      Sparse22
        (insert (liftLiveEdge (Flag := Flag) f)
          (deleteVertexEdges
            (deleteVertexEdges S.completionEdges (Sum.inr t))
            (Sum.inl v))) := by
  let Q := deleteVertexEdges
    (deleteVertexEdges S.completionEdges (Sum.inr t)) (Sum.inl v)
  let epz : SimpleEdge V := simpleEdge p z hpz
  let eqz : SimpleEdge V := simpleEdge q z hqz
  let epzHat : SimpleEdge (V ⊕ Flag) := liftLiveEdge (Flag := Flag) epz
  let eqzHat : SimpleEdge (V ⊕ Flag) := liftLiveEdge (Flag := Flag) eqz
  have hQSub : Q ⊆ S.completionEdges :=
    (deleteVertexEdges_subset _ _).trans (deleteVertexEdges_subset _ _)
  have hQSparse : Sparse22 Q := hSparse.mono hQSub
  have hpT : p ∈ S.terminals t := by rw [hTerminals]; simp
  have hqT : q ∈ S.terminals t := by rw [hTerminals]; simp
  have hvT : v ∈ S.terminals t := by rw [hTerminals]; simp
  have hpqCompletion :
      liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
        S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact hpqLive
  have hvzCompletion :
      liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ∈
        S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    rw [S.mem_liftedLiveEdges]
    exact hvzLive
  have hpqQ :
      liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨hpqCompletion, ?_⟩, ?_⟩
    · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvp, hvq]
  have candidate_mem_Q_of_mem_completion_pz
      (h : epzHat ∈ S.completionEdges) : epzHat ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨h, ?_⟩, ?_⟩
    · dsimp [epzHat, epz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · dsimp [epzHat, epz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvp, hvz]
  have candidate_mem_Q_of_mem_completion_qz
      (h : eqzHat ∈ S.completionEdges) : eqzHat ∈ Q := by
    apply mem_deleteVertexEdges.mpr
    refine ⟨mem_deleteVertexEdges.mpr ⟨h, ?_⟩, ?_⟩
    · dsimp [eqzHat, eqz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp
    · dsimp [eqzHat, eqz]
      rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
      simp [hvq, hvz]
  have noBoth : ¬ (epzHat ∈ Q ∧ eqzHat ∈ Q) := by
    rintro ⟨hpzQ, hqzQ⟩
    let Kt := S.flagVertices t
    have hzKt : Sum.inl z ∉ Kt := by
      change Sum.inl z ∉ S.flagVertices t
      rw [S.mem_flagVertices_live, hTerminals]
      simp [Ne.symm hvz, Ne.symm hpz, Ne.symm hqz]
    have hpzCompletion : epzHat ∈ S.completionEdges := hQSub hpzQ
    have hqzCompletion : eqzHat ∈ S.completionEdges := hQSub hqzQ
    have hvzNew :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ∈
          newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hvzCompletion, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t v).2 hvT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hpzNew : epzHat ∈
        newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hpzCompletion, ?_, ?_⟩
      · dsimp [epzHat, epz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t p).2 hpT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hqzNew : eqzHat ∈
        newEdgesAt S.completionEdges Kt (Sum.inl z) := by
      rw [mem_newEdgesAt]
      refine ⟨hqzCompletion, ?_, ?_⟩
      · dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem
            ((S.mem_flagVertices_live t q).2 hqT),
          Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hzKt (hsub (by
          dsimp [eqzHat, eqz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hvz_ne_pz :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ≠ epzHat := by
      intro hEq
      have hLive : simpleEdge v z hvz = epz := liftLiveEdge_injective hEq
      dsimp [epz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hvp h.1
      · exact hvz h.1
    have hvz_ne_qz :
        liftLiveEdge (Flag := Flag) (simpleEdge v z hvz) ≠ eqzHat := by
      intro hEq
      have hLive : simpleEdge v z hvz = eqz := liftLiveEdge_injective hEq
      dsimp [eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hvq h.1
      · exact hvz h.1
    have hpz_ne_qz : epzHat ≠ eqzHat := by
      intro hEq
      have hLive : epz = eqz := liftLiveEdge_injective hEq
      dsimp [epz, eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hpq h.1
      · exact hpz h.1
    have hThree : 3 ≤
        (newEdgesAt S.completionEdges Kt (Sum.inl z)).card :=
      three_le_card_of_triple_subset hvz_ne_pz hvz_ne_qz hpz_ne_qz (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hvzNew
        · exact hpzNew
        · exact hqzNew)
    have hAtMostTwo :
        (newEdgesAt S.completionEdges Kt (Sum.inl z)).card ≤ 2 := by
      simpa only [Kt] using card_newEdgesAt_le_two hSparse
        (S.flagVertices_tight hSparse t) hzKt
    omega
  have extend_by_p_tight
      (U : Finset (V ⊕ Flag))
      (hU : Tight22 Q U)
      (hqU : Sum.inl q ∈ U) (hzU : Sum.inl z ∈ U)
      (hpU : Sum.inl p ∉ U) (hpzQ : epzHat ∈ Q) :
      Tight22 Q (insert (Sum.inl p) U) := by
    have hpqNew :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
          newEdgesAt Q U (Sum.inl p) := by
      rw [mem_newEdgesAt]
      refine ⟨hpqQ, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hqU⟩
      · intro hsub
        exact hpU (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hpzNew : epzHat ∈ newEdgesAt Q U (Sum.inl p) := by
      rw [mem_newEdgesAt]
      refine ⟨hpzQ, ?_, ?_⟩
      · dsimp [epzHat, epz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hzU⟩
      · intro hsub
        exact hpU (hsub (by
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hEdgesNe :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ≠ epzHat := by
      intro hEq
      have hLive : simpleEdge p q hpq = epz := liftLiveEdge_injective hEq
      dsimp [epz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hqz h.2
      · exact hpz h.1
    have hLower : 2 ≤ (newEdgesAt Q U (Sum.inl p)).card :=
      two_le_card_of_pair_subset hEdgesNe (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hpqNew
        · exact hpzNew)
    have hUpper := card_newEdgesAt_le_two hQSparse hU hpU
    apply tight22_insert_of_card_newEdgesAt_eq_two hU hpU
    omega
  have extend_by_q_tight
      (U : Finset (V ⊕ Flag))
      (hU : Tight22 Q U)
      (hpU : Sum.inl p ∈ U) (hzU : Sum.inl z ∈ U)
      (hqU : Sum.inl q ∉ U) (hqzQ : eqzHat ∈ Q) :
      Tight22 Q (insert (Sum.inl q) U) := by
    have hpqNew :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ∈
          newEdgesAt Q U (Sum.inl q) := by
      rw [mem_newEdgesAt]
      refine ⟨hpqQ, ?_, ?_⟩
      · rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem hpU, Finset.mem_insert_self _ _⟩
      · intro hsub
        exact hqU (hsub (by rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]; simp))
    have hqzNew : eqzHat ∈ newEdgesAt Q U (Sum.inl q) := by
      rw [mem_newEdgesAt]
      refine ⟨hqzQ, ?_, ?_⟩
      · dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hzU⟩
      · intro hsub
        exact hqU (hsub (by
          dsimp [eqzHat, eqz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp))
    have hEdgesNe :
        liftLiveEdge (Flag := Flag) (simpleEdge p q hpq) ≠ eqzHat := by
      intro hEq
      have hLive : simpleEdge p q hpq = eqz := liftLiveEdge_injective hEq
      dsimp [eqz] at hLive
      rw [simpleEdge_eq_simpleEdge_iff] at hLive
      rcases hLive with h | h
      · exact hpq h.1
      · exact hpz h.1
    have hLower : 2 ≤ (newEdgesAt Q U (Sum.inl q)).card :=
      two_le_card_of_pair_subset hEdgesNe (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hpqNew
        · exact hqzNew)
    have hUpper := card_newEdgesAt_le_two hQSparse hU hqU
    apply tight22_insert_of_card_newEdgesAt_eq_two hU hqU
    omega
  by_cases hpzQ : epzHat ∈ Q
  · have hqzQ : eqzHat ∉ Q := fun h ↦ noBoth ⟨hpzQ, h⟩
    by_cases hAdd : Sparse22 (insert eqzHat Q)
    · refine ⟨eqz, Or.inr rfl, ?_, hAdd⟩
      intro hParent
      exact hqzQ (candidate_mem_Q_of_mem_completion_qz hParent)
    · obtain ⟨U, _hUne, hqzU, hUTight⟩ :=
        exists_tight22_of_not_sparse22_insert hQSparse hqzQ hAdd
      have hqU : Sum.inl q ∈ U := by
        apply hqzU
        dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        simp
      have hzU : Sum.inl z ∈ U := by
        apply hqzU
        dsimp [eqzHat, eqz]
        rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
        simp
      by_cases hpU : Sum.inl p ∈ U
      · exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
          hSparse v p q t hvp hvq hpq hTerminals U hUTight hpU hqU).elim
      · have hInsertTight :=
          extend_by_p_tight U hUTight hqU hzU hpU hpzQ
        exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
          hSparse v p q t hvp hvq hpq hTerminals (insert (Sum.inl p) U)
          hInsertTight (by simp) (by simp [hqU])).elim
  · by_cases hqzQ : eqzHat ∈ Q
    · by_cases hAdd : Sparse22 (insert epzHat Q)
      · refine ⟨epz, Or.inl rfl, ?_, hAdd⟩
        intro hParent
        exact hpzQ (candidate_mem_Q_of_mem_completion_pz hParent)
      · obtain ⟨U, _hUne, hpzU, hUTight⟩ :=
          exists_tight22_of_not_sparse22_insert hQSparse hpzQ hAdd
        have hpU : Sum.inl p ∈ U := by
          apply hpzU
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp
        have hzU : Sum.inl z ∈ U := by
          apply hpzU
          dsimp [epzHat, epz]
          rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
          simp
        by_cases hqU : Sum.inl q ∈ U
        · exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals U hUTight hpU hqU).elim
        · have hInsertTight :=
            extend_by_q_tight U hUTight hpU hzU hqU hqzQ
          exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals (insert (Sum.inl q) U)
            hInsertTight (by simp [hpU]) (by simp)).elim
    · by_cases hAddP : Sparse22 (insert epzHat Q)
      · refine ⟨epz, Or.inl rfl, ?_, hAddP⟩
        intro hParent
        exact hpzQ (candidate_mem_Q_of_mem_completion_pz hParent)
      · by_cases hAddQ : Sparse22 (insert eqzHat Q)
        · refine ⟨eqz, Or.inr rfl, ?_, hAddQ⟩
          intro hParent
          exact hqzQ (candidate_mem_Q_of_mem_completion_qz hParent)
        · obtain ⟨Up, _hUpNe, hpzUp, hUpTight⟩ :=
            exists_tight22_of_not_sparse22_insert hQSparse hpzQ hAddP
          obtain ⟨Uq, _hUqNe, hqzUq, hUqTight⟩ :=
            exists_tight22_of_not_sparse22_insert hQSparse hqzQ hAddQ
          have hpUp : Sum.inl p ∈ Up := by
            apply hpzUp
            dsimp [epzHat, epz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hzUp : Sum.inl z ∈ Up := by
            apply hpzUp
            dsimp [epzHat, epz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hqUq : Sum.inl q ∈ Uq := by
            apply hqzUq
            dsimp [eqzHat, eqz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hzUq : Sum.inl z ∈ Uq := by
            apply hqzUq
            dsimp [eqzHat, eqz]
            rw [liftLiveEdge_simpleEdge, vertices_simpleEdge]
            simp
          have hInterNonempty : (Up ∩ Uq).Nonempty :=
            ⟨Sum.inl z, Finset.mem_inter.mpr ⟨hzUp, hzUq⟩⟩
          have hUnionTight :=
            (tight22_union_inter hQSparse hUpTight hUqTight hInterNonempty).1
          exact (S.no_tightSet_in_privateDoubleDelete_containing_endpoints
            hSparse v p q t hvp hvq hpq hTerminals (Up ∪ Uq)
            hUnionTight (Finset.mem_union_left _ hpUp)
            (Finset.mem_union_right _ hqUq)).elim

end ProvenanceFlag

end

end RB31E2E
