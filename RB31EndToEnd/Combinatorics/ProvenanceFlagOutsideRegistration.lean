import RB31EndToEnd.Combinatorics.ProvenanceFlagOutsideMove
import RB31EndToEnd.Combinatorics.ProvenanceFlagPrivateDeletion

/-!
# Registering an outside complete triangle as a new provenance flag

The complete branch of the outside move is only usable if the three
neighbour edges in the completion are genuine live edges.  This file first
proves that fact.  If one of them were a restored edge of an old flag, the
old completed `K₄` is tight.  Adding the outside apex acquires two edges;
adding the third neighbour then acquires three, contradicting `(2,2)`
sparsity.

The subsequent state constructor will replace the deleted outside apex by
the private ghost of a new flag.  No provenance conclusion is assumed as a
field of `State`.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlag

variable {V Flag : Type*}
  [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag]

/-- Two named distinct edges give a two-edge lower bound. -/
private theorem two_le_card_of_pair_subset
    {W : Type*} [DecidableEq W] {F : SimpleEdgeSet W}
    {e f : SimpleEdge W} (hef : e ≠ f)
    (hsub : ({e, f} : SimpleEdgeSet W) ⊆ F) :
    2 ≤ F.card := by
  have hcard : ({e, f} : SimpleEdgeSet W).card = 2 := by simp [hef]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Three named pairwise distinct edges give a three-edge lower bound. -/
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

/-- Two neighbours of a completed outside degree-three apex cannot both
belong to one already active terminal triple. -/
theorem State.outside_complete_pair_not_both_terminals
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v a b c : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvOutside : S.flagMultiplicity v = 0)
    (hvaLive : simpleEdge v a hva ∈ S.edges)
    (hvbLive : simpleEdge v b hvb ∈ S.edges)
    (hvcLive : simpleEdge v c hvc ∈ S.edges)
    (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
      S.completionEdges)
    (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
      S.completionEdges)
    (t : Flag) (haT : a ∈ S.terminals t) (hbT : b ∈ S.terminals t) :
    False := by
  let K : Finset (V ⊕ Flag) := S.flagVertices t
  have hKTight : Tight22 S.completionEdges K :=
    S.flagVertices_tight hSparse t
  have hvK : Sum.inl v ∉ K := by
    intro hv
    exact (not_mem_terminals_of_flagMultiplicity_eq_zero S v hvOutside t)
      ((S.mem_flagVertices_live t v).1 hv)
  have haK : Sum.inl a ∈ K := (S.mem_flagVertices_live t a).2 haT
  have hbK : Sum.inl b ∈ K := (S.mem_flagVertices_live t b).2 hbT
  let eva : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl a) (by simpa using hva)
  let evb : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl b) (by simpa using hvb)
  let evc : SimpleEdge (V ⊕ Flag) :=
    simpleEdge (Sum.inl v) (Sum.inl c) (by simpa using hvc)
  have hvaCompletion : eva ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v a hva) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvaLive
  have hvbCompletion : evb ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v b hvb) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvbLive
  have hvcCompletion : evc ∈ S.completionEdges := by
    apply S.liftedLiveEdges_subset_completionEdges
    change liftLiveEdge (Flag := Flag) (simpleEdge v c hvc) ∈
      S.liftedLiveEdges
    rw [S.mem_liftedLiveEdges]
    exact hvcLive
  have hvaNew : eva ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
    rw [mem_newEdgesAt]
    refine ⟨hvaCompletion, ?_, ?_⟩
    · rw [vertices_simpleEdge]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem haK⟩
    · intro hsub
      exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
  have hvbNew : evb ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
    rw [mem_newEdgesAt]
    refine ⟨hvbCompletion, ?_, ?_⟩
    · rw [vertices_simpleEdge]
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbK⟩
    · intro hsub
      exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
  have hevaevb : eva ≠ evb := by
    simp [eva, evb, simpleEdge_eq_simpleEdge_iff, hab, hvb]
  have hTwoLower :
      2 ≤ (newEdgesAt S.completionEdges K (Sum.inl v)).card :=
    two_le_card_of_pair_subset hevaevb (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hvaNew
      · exact hvbNew)
  have hTwoUpper := card_newEdgesAt_le_two hSparse hKTight hvK
  have hTwo :
      (newEdgesAt S.completionEdges K (Sum.inl v)).card = 2 := by omega
  by_cases hcK : Sum.inl c ∈ K
  · have hvcNew : evc ∈ newEdgesAt S.completionEdges K (Sum.inl v) := by
      rw [mem_newEdgesAt]
      refine ⟨hvcCompletion, ?_, ?_⟩
      · rw [vertices_simpleEdge]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hcK⟩
      · intro hsub
        exact hvK (hsub (by rw [vertices_simpleEdge]; simp))
    have hevac : eva ≠ evc := by
      simp [eva, evc, simpleEdge_eq_simpleEdge_iff, hac, hvc]
    have hevbc : evb ≠ evc := by
      simp [evb, evc, simpleEdge_eq_simpleEdge_iff, hbc, hvc]
    have hThree :
        3 ≤ (newEdgesAt S.completionEdges K (Sum.inl v)).card :=
      three_le_card_of_triple_subset hevaevb hevac hevbc (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hvaNew
        · exact hvbNew
        · exact hvcNew)
    omega
  · let K' := insert (Sum.inl v) K
    have hK'Tight : Tight22 S.completionEdges K' :=
      tight22_insert_of_card_newEdgesAt_eq_two hKTight hvK hTwo
    have hcK' : Sum.inl c ∉ K' := by simp [K', hcK, hvc.symm]
    let eca : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl a) (by simpa using hac.symm)
    let ecb : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl b) (by simpa using hbc.symm)
    let ecv : SimpleEdge (V ⊕ Flag) :=
      simpleEdge (Sum.inl c) (Sum.inl v) (by simpa using hvc.symm)
    have hcaCompletion : eca ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl a) (by simpa using hac.symm) ∈ _
      rw [simpleEdge_comm]
      simpa only [liftLiveEdge_simpleEdge] using hacComplete
    have hcbCompletion : ecb ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl b) (by simpa using hbc.symm) ∈ _
      rw [simpleEdge_comm]
      simpa only [liftLiveEdge_simpleEdge] using hbcComplete
    have hcvCompletion : ecv ∈ S.completionEdges := by
      change simpleEdge (Sum.inl c) (Sum.inl v) (by simpa using hvc.symm) ∈ _
      rw [simpleEdge_comm]
      exact hvcCompletion
    have edgeFromCNew (x : V) (hcx : c ≠ x)
        (hxK' : Sum.inl x ∈ K')
        (hmem : simpleEdge (Sum.inl c) (Sum.inl x)
          (by simpa using hcx) ∈ S.completionEdges) :
        simpleEdge (Sum.inl c) (Sum.inl x)
            (by simpa using hcx) ∈
          newEdgesAt S.completionEdges K' (Sum.inl c) := by
      rw [mem_newEdgesAt]
      refine ⟨hmem, ?_, ?_⟩
      · rw [vertices_simpleEdge]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxK'⟩
      · intro hsub
        exact hcK' (hsub (by rw [vertices_simpleEdge]; simp))
    have hcaNew : eca ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew a hac.symm (by simp [K', haK]) hcaCompletion
    have hcbNew : ecb ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew b hbc.symm (by simp [K', hbK]) hcbCompletion
    have hcvNew : ecv ∈ newEdgesAt S.completionEdges K' (Sum.inl c) :=
      edgeFromCNew v hvc.symm (by simp [K']) hcvCompletion
    have hca_cb : eca ≠ ecb := by
      simp [eca, ecb, simpleEdge_eq_simpleEdge_iff, hab, hbc.symm]
    have hca_cv : eca ≠ ecv := by
      simp [eca, ecv, simpleEdge_eq_simpleEdge_iff, hvc.symm, hva.symm]
    have hcb_cv : ecb ≠ ecv := by
      simp [ecb, ecv, simpleEdge_eq_simpleEdge_iff, hvc.symm, hvb.symm]
    have hThree :
        3 ≤ (newEdgesAt S.completionEdges K' (Sum.inl c)).card :=
      three_le_card_of_triple_subset hca_cb hca_cv hcb_cv (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hcaNew
        · exact hcbNew
        · exact hcvNew)
    have hAtMostTwo := card_newEdgesAt_le_two hSparse hK'Tight hcK'
    omega

/-- In particular, a completed neighbour pair cannot be the restored
missing edge of an old flag. -/
theorem State.outside_complete_pair_ne_missing
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v a b c : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hvOutside : S.flagMultiplicity v = 0)
    (hvaLive : simpleEdge v a hva ∈ S.edges)
    (hvbLive : simpleEdge v b hvb ∈ S.edges)
    (hvcLive : simpleEdge v c hvc ∈ S.edges)
    (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
      S.completionEdges)
    (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
      S.completionEdges)
    (t : Flag) :
    simpleEdge a b hab ≠ S.missing t := by
  intro habMissing
  apply S.outside_complete_pair_not_both_terminals hSparse v a b c
    hva hvb hvc hab hac hbc hvOutside hvaLive hvbLive hvcLive
    hacComplete hbcComplete t
  · apply S.missing_supported t
    rw [← habMissing, vertices_simpleEdge]
    simp
  · apply S.missing_supported t
    rw [← habMissing, vertices_simpleEdge]
    simp

/-- Hence every completed edge of the outside neighbour triangle is live. -/
theorem State.outside_complete_triangle_live
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hComplete :
      liftLiveEdge (Flag := Flag) (simpleEdge N.p N.q N.hpq) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.p N.r N.hpr) ∈
          S.completionEdges ∧
        liftLiveEdge (Flag := Flag) (simpleEdge N.q N.r N.hqr) ∈
          S.completionEdges) :
    simpleEdge N.p N.q N.hpq ∈ S.edges ∧
      simpleEdge N.p N.r N.hpr ∈ S.edges ∧
      simpleEdge N.q N.r N.hqr ∈ S.edges := by
  have pairLive (a b c : V)
      (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hvaLive : simpleEdge v a hva ∈ S.edges)
      (hvbLive : simpleEdge v b hvb ∈ S.edges)
      (hvcLive : simpleEdge v c hvc ∈ S.edges)
      (habComplete : liftLiveEdge (Flag := Flag) (simpleEdge a b hab) ∈
        S.completionEdges)
      (hacComplete : liftLiveEdge (Flag := Flag) (simpleEdge a c hac) ∈
        S.completionEdges)
      (hbcComplete : liftLiveEdge (Flag := Flag) (simpleEdge b c hbc) ∈
        S.completionEdges) :
      simpleEdge a b hab ∈ S.edges := by
    rw [State.completionEdges] at habComplete
    rcases Finset.mem_union.mp habComplete with habLM | habGhost
    · rcases Finset.mem_union.mp habLM with habLive | habMissing
      · exact (S.mem_liftedLiveEdges _).1 habLive
      · obtain ⟨t, _ht, htEq⟩ := Finset.mem_image.mp habMissing
        have hEq : simpleEdge a b hab = S.missing t :=
          liftLiveEdge_injective htEq.symm
        exact (S.outside_complete_pair_ne_missing hSparse v a b c
          hva hvb hvc hab hac hbc hvOutside hvaLive hvbLive hvcLive
          hacComplete hbcComplete t hEq).elim
    · obtain ⟨t, _ht, hstar⟩ := Finset.mem_biUnion.mp habGhost
      obtain ⟨x, _hx, hEq⟩ := Finset.mem_image.mp hstar
      have hVertices := congrArg SimpleEdge.vertices hEq
      rw [vertices_ghostEdge, liftLiveEdge_simpleEdge,
        vertices_simpleEdge] at hVertices
      have : Sum.inr t ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ Flag)) := by
        rw [← hVertices]
        simp
      simp at this
  refine ⟨?_, ?_, ?_⟩
  · exact pairLive N.p N.q N.r N.hvp N.hvq N.hvr
      N.hpq N.hpr N.hqr N.vp_mem N.vq_mem N.vr_mem
      hComplete.1 hComplete.2.1 hComplete.2.2
  · exact pairLive N.p N.r N.q N.hvp N.hvr N.hvq
      N.hpr N.hpq N.hqr.symm N.vp_mem N.vr_mem N.vq_mem
      hComplete.2.1 hComplete.1
      (by rw [simpleEdge_comm]; exact hComplete.2.2)
  · exact pairLive N.q N.r N.p N.hvq N.hvr N.hvp
      N.hqr N.hpq.symm N.hpr.symm N.vq_mem N.vr_mem N.vp_mem
      hComplete.2.2
      (by rw [simpleEdge_comm]; exact hComplete.1)
      (by rw [simpleEdge_comm]; exact hComplete.2.1)

/-! ## Literal registration of the new outside flag -/

/-- After deleting the outside apex, the three retained neighbours form
the terminal set of the newly registered flag. -/
def State.registerOutside
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    State (RemainingVertex v) (Flag ⊕ Unit) where
  edges := (restrictedLiveEdges S.edges v).erase
    (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
      (not_mem_degreeThreeNeighbourPair N _ (by simp)))
  terminals
    | Sum.inl t => (S.deleteOutside v hvOutside).terminals t
    | Sum.inr _ =>
        {⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩, ⟨N.r, N.hvr.symm⟩}
  missing
    | Sum.inl t => (S.deleteOutside v hvOutside).missing t
    | Sum.inr _ => restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
        (not_mem_degreeThreeNeighbourPair N _ (by simp))
  terminals_card
    | Sum.inl t => (S.deleteOutside v hvOutside).terminals_card t
    | Sum.inr _ => by simp [N.hpq, N.hpr, N.hqr]
  missing_supported
    | Sum.inl t => (S.deleteOutside v hvOutside).missing_supported t
    | Sum.inr _ => by
        intro x hx
        rw [mem_restrictSimpleEdge_vertices_iff] at hx
        rw [vertices_simpleEdge] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with hx | hx
        · left
          exact Subtype.ext hx
        · right; left
          exact Subtype.ext hx
  missing_not_live
    | Sum.inl t => by
        exact Finset.not_mem_subset (Finset.erase_subset _ _)
          ((S.deleteOutside v hvOutside).missing_not_live t)
    | Sum.inr _ => by simp
  other_terminal_edges_live
    | Sum.inl t => fun e heT heMissing ↦ by
        apply Finset.mem_erase.mpr
        refine ⟨?_, (S.deleteOutside v hvOutside).other_terminal_edges_live
          t e heT heMissing⟩
        intro heq
        have hpChild : (⟨N.p, N.hvp.symm⟩ : RemainingVertex v) ∈
            e.vertices := by
          rw [heq, mem_restrictSimpleEdge_vertices_iff,
            vertices_simpleEdge]
          simp
        have hqChild : (⟨N.q, N.hvq.symm⟩ : RemainingVertex v) ∈
            e.vertices := by
          rw [heq, mem_restrictSimpleEdge_vertices_iff,
            vertices_simpleEdge]
          simp
        have hpTChild := heT hpChild
        have hqTChild := heT hqChild
        have hpT : N.p ∈ S.terminals t :=
          (mem_restrictVertexSet_iff v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero
              S v hvOutside t) _).1 hpTChild
        have hqT : N.q ∈ S.terminals t :=
          (mem_restrictVertexSet_iff v (S.terminals t)
            (not_mem_terminals_of_flagMultiplicity_eq_zero
              S v hvOutside t) _).1 hqTChild
        have hprComplete : liftLiveEdge (Flag := Flag)
            (simpleEdge N.p N.r N.hpr) ∈ S.completionEdges := by
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.2.1
        have hqrComplete : liftLiveEdge (Flag := Flag)
            (simpleEdge N.q N.r N.hqr) ∈ S.completionEdges := by
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.2.2
        exact S.outside_complete_pair_not_both_terminals hSparse
          v N.p N.q N.r N.hvp N.hvq N.hvr N.hpq N.hpr N.hqr
          hvOutside N.vp_mem N.vq_mem N.vr_mem hprComplete hqrComplete
          t hpT hqT
    | Sum.inr _ => fun e heT heMissing ↦ by
        apply Finset.mem_erase.mpr
        refine ⟨heMissing, ?_⟩
        rw [mem_restrictedLiveEdges_iff]
        apply mem_deleteVertexEdges.mpr
        refine ⟨?_, deleted_not_mem_mapped_vertices v e⟩
        have heVertices : e.vertices =
            ({⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩} :
              Finset (RemainingVertex v)) ∨
          e.vertices = {⟨N.p, N.hvp.symm⟩, ⟨N.r, N.hvr.symm⟩} ∨
          e.vertices = {⟨N.q, N.hvq.symm⟩, ⟨N.r, N.hvr.symm⟩} := by
          have hsMem : e.source ∈ e.vertices := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          have htMem : e.target ∈ e.vertices := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          have hs := heT hsMem
          have ht := heT htMem
          have hst := e.source_ne_target
          have hverts : e.vertices = {e.source, e.target} := by
            rw [SimpleEdge.vertices, ← e.source_target_mk]
            simp [Sym2.toFinset_mk_eq]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
          rcases hs with hs | hs | hs <;>
            rcases ht with ht | ht | ht <;>
            simp_all [Finset.pair_comm]
        rcases heVertices with hPQ | hPR | hQR
        · exfalso
          apply heMissing
          apply SimpleEdge.eq_of_vertices_eq
          rw [hPQ]
          ext x
          rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
          simp [Subtype.ext_iff]
        · have hMap : Sparse22Transport.mapSimpleEdge
              (remainingVertexEmbedding v) e = simpleEdge N.p N.r N.hpr := by
            have heq : e = restrictSimpleEdge v
                (simpleEdge N.p N.r N.hpr)
                (not_mem_degreeThreeNeighbourPair N _ (by simp)) := by
              apply SimpleEdge.eq_of_vertices_eq
              rw [hPR]
              ext x
              rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
              simp [Subtype.ext_iff]
            rw [heq, map_restrictSimpleEdge]
          rw [hMap]
          exact hTriangleLive.2.1
        · have hMap : Sparse22Transport.mapSimpleEdge
              (remainingVertexEmbedding v) e = simpleEdge N.q N.r N.hqr := by
            have heq : e = restrictSimpleEdge v
                (simpleEdge N.q N.r N.hqr)
                (not_mem_degreeThreeNeighbourPair N _ (by simp)) := by
              apply SimpleEdge.eq_of_vertices_eq
              rw [hQR]
              ext x
              rw [mem_restrictSimpleEdge_vertices_iff, vertices_simpleEdge]
              simp [Subtype.ext_iff]
            rw [heq, map_restrictSimpleEdge]
          rw [hMap]
          exact hTriangleLive.2.2

/-! ## Completion transport for the registered child -/

/-- The completion of the registered child embeds in the old completion by
sending the new private ghost back to the deleted outside apex. -/
def registeredCompletionEmbedding (v : V) :
    (RemainingVertex v ⊕ (Flag ⊕ Unit)) ↪ (V ⊕ Flag) where
  toFun
    | Sum.inl u => Sum.inl u.1
    | Sum.inr (Sum.inl t) => Sum.inr t
    | Sum.inr (Sum.inr _) => Sum.inl v
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            change Sum.inl (x.1 : V) = Sum.inl (y.1 : V) at hxy
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hxy))
        | inr y =>
            cases y with
            | inl y => exact False.elim (Sum.inl_ne_inr hxy)
            | inr y =>
                change Sum.inl (x.1 : V) = Sum.inl v at hxy
                exact False.elim (x.2 (Sum.inl.inj hxy))
    | inr x =>
        cases x with
        | inl x =>
            cases y with
            | inl y => exact False.elim (Sum.inr_ne_inl hxy)
            | inr y =>
                cases y with
                | inl y =>
                    change Sum.inr x = Sum.inr y at hxy
                    exact congrArg (fun z => Sum.inr (Sum.inl z))
                      (Sum.inr.inj hxy)
                | inr y => exact False.elim (Sum.inr_ne_inl hxy)
        | inr x =>
            cases y with
            | inl y =>
                change Sum.inl v = Sum.inl (y.1 : V) at hxy
                exact False.elim (y.2 (Sum.inl.inj hxy).symm)
            | inr y =>
                cases y with
                | inl y => exact False.elim (Sum.inl_ne_inr hxy)
                | inr y =>
                    cases x
                    cases y
                    rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_liftLiveEdge_registered
    (v : V) (e : SimpleEdge (RemainingVertex v)) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag ⊕ Unit) e) =
      liftLiveEdge (Flag := Flag)
        (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v) e) := by
  apply Subtype.ext
  simp only [Sparse22Transport.mapSimpleEdge_val, liftLiveEdge_val,
    Sym2.map_map]
  induction e.1 using Sym2.inductionOn with
  | _ a b =>
      simp [registeredCompletionEmbedding, remainingVertexEmbedding]

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_registered_old
    (v : V) (t : Flag) (x : RemainingVertex v) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (ghostEdge (Sum.inl t) x) = ghostEdge t x.1 := by
  apply Subtype.ext
  change s(Sum.inr t, Sum.inl x.1) = s(Sum.inr t, Sum.inl x.1)
  rfl

omit [Fintype V] [DecidableEq V] [Fintype Flag] [DecidableEq Flag] in
private theorem map_ghostEdge_registered_new
    (v : V) (x : RemainingVertex v) :
    Sparse22Transport.mapSimpleEdge (registeredCompletionEmbedding
        (Flag := Flag) v)
        (ghostEdge (Sum.inr ()) x) =
      liftLiveEdge (Flag := Flag) (simpleEdge v x.1 x.2.symm) := by
  apply Subtype.ext
  change s(Sum.inl v, Sum.inl x.1) = s(Sum.inl v, Sum.inl x.1)
  rfl

@[simp]
theorem State.registerOutside_edges
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    (S.registerOutside hSparse v hvOutside N hTriangleLive).edges =
      (restrictedLiveEdges S.edges v).erase
        (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
          (not_mem_degreeThreeNeighbourPair N _ (by simp))) := rfl

/-- Every completed edge of the registered child maps to an edge of the
old completion.  The new ghost star maps exactly to the deleted apex star,
and the newly restored missing edge maps to the old live `pq` edge. -/
theorem State.map_registerOutside_completionEdges_subset
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    Sparse22Transport.mapEdgeSet
        (registeredCompletionEmbedding (Flag := Flag) v)
        (S.registerOutside hSparse v hvOutside N hTriangleLive).completionEdges ⊆
      S.completionEdges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [State.completionEdges] at hf
  rcases Finset.mem_union.mp hf with hfLiveOrMissing | hfGhost
  · rcases Finset.mem_union.mp hfLiveOrMissing with hfLive | hfMissing
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hfLive
      change Sparse22Transport.mapSimpleEdge
        (registeredCompletionEmbedding (Flag := Flag) v)
        (liftLiveEdge (Flag := Flag ⊕ Unit) g) ∈ S.completionEdges
      rw [map_liftLiveEdge_registered]
      apply S.liftedLiveEdges_subset_completionEdges
      rw [S.mem_liftedLiveEdges]
      have hgRestricted : g ∈ restrictedLiveEdges S.edges v := by
        exact Finset.mem_of_mem_erase hg
      exact (mem_deleteVertexEdges.mp
        ((mem_restrictedLiveEdges_iff S.edges v g).1 hgRestricted)).1
    · obtain ⟨t, _ht, hft⟩ := Finset.mem_image.mp hfMissing
      subst f
      cases t with
      | inl t =>
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                ((S.registerOutside hSparse v hvOutside N
                  hTriangleLive).missing (Sum.inl t))) ∈ S.completionEdges
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                ((S.deleteOutside v hvOutside).missing t)) ∈ S.completionEdges
          rw [map_liftLiveEdge_registered]
          change liftLiveEdge (Flag := Flag)
              (Sparse22Transport.mapSimpleEdge (remainingVertexEmbedding v)
                (restrictSimpleEdge v (S.missing t)
                  (outside_not_mem_missing_vertices S v hvOutside t))) ∈
            S.completionEdges
          rw [map_restrictSimpleEdge]
          exact S.lifted_missing_mem_completionEdges t
      | inr t =>
          cases t
          change Sparse22Transport.mapSimpleEdge
              (registeredCompletionEmbedding (Flag := Flag) v)
              (liftLiveEdge (Flag := Flag ⊕ Unit)
                (restrictSimpleEdge v (simpleEdge N.p N.q N.hpq)
                  (not_mem_degreeThreeNeighbourPair N _ (by simp)))) ∈
            S.completionEdges
          rw [map_liftLiveEdge_registered, map_restrictSimpleEdge]
          apply S.liftedLiveEdges_subset_completionEdges
          rw [S.mem_liftedLiveEdges]
          exact hTriangleLive.1
  · obtain ⟨t, _ht, hfStar⟩ := Finset.mem_biUnion.mp hfGhost
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hfStar
    subst f
    cases t with
    | inl t =>
        change Sparse22Transport.mapSimpleEdge
          (registeredCompletionEmbedding (Flag := Flag) v)
          (ghostEdge (Sum.inl t) x) ∈ S.completionEdges
        rw [map_ghostEdge_registered_old]
        apply S.ghostEdge_mem_completionEdges t
        exact (mem_restrictVertexSet_iff v (S.terminals t)
          (not_mem_terminals_of_flagMultiplicity_eq_zero
            S v hvOutside t) x).1 hx
    | inr t =>
        cases t
        change Sparse22Transport.mapSimpleEdge
          (registeredCompletionEmbedding (Flag := Flag) v)
          (ghostEdge (Sum.inr ()) x) ∈ S.completionEdges
        rw [map_ghostEdge_registered_new]
        apply S.liftedLiveEdges_subset_completionEdges
        rw [S.mem_liftedLiveEdges]
        change x ∈
          ({⟨N.p, N.hvp.symm⟩, ⟨N.q, N.hvq.symm⟩,
            ⟨N.r, N.hvr.symm⟩} : Finset (RemainingVertex v)) at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · have hx' : x = ⟨N.p, N.hvp.symm⟩ := hx
          subst x
          exact N.vp_mem
        · have hx' : x = ⟨N.q, N.hvq.symm⟩ := hx
          subst x
          exact N.vq_mem
        · have hx' : x = ⟨N.r, N.hvr.symm⟩ := hx
          subst x
          exact N.vr_mem

/-- Registering the complete outside triangle preserves literal completion
`(2,2)`-sparsity. -/
theorem State.registerOutside_completionSparse
    (S : State V Flag) (hSparse : S.CompletionSparse)
    (v : V) (hvOutside : S.flagMultiplicity v = 0)
    (N : DirectionStress.DegreeThreeNeighbours S.edges v)
    (hTriangleLive :
      simpleEdge N.p N.q N.hpq ∈ S.edges ∧
        simpleEdge N.p N.r N.hpr ∈ S.edges ∧
        simpleEdge N.q N.r N.hqr ∈ S.edges) :
    (S.registerOutside hSparse v hvOutside N hTriangleLive).CompletionSparse := by
  exact Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (registeredCompletionEmbedding (Flag := Flag) v) hSparse
    (S.map_registerOutside_completionEdges_subset
      hSparse v hvOutside N hTriangleLive)

end ProvenanceFlag

end

end RB31E2E
