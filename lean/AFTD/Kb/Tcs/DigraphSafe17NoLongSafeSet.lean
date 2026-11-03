import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphSafe17Structure
import AFTD.Kb.Tcs.DigraphOrientedSafeSetIndegreeBound

/-!
# digraph_safe17_no_long_safe_set

Topic: graphs   Node: 5cc686598f20

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

Every proper set of at least five vertices in the displayed graph has an outside vertex with at least three outneighbors in the set.
-/

private instance in504_safe17_final_decAdj_0 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe17_no_long_safe_set
    (C : Finset (Fin 17)) (hne : ∃ v, v ∉ C) (hlarge : 5 ≤ C.card)
    (hsafe : ∀ v ∉ C, (C.filter fun w => digraph_safe17_graph.Adj v w).card ≤ 2) : False := by
  classical
  obtain ⟨hloop,hori,hout,hin,hcommon⟩ := digraph_safe17_structure
  have hc : C.card ≤ 17 := by
    have h := Finset.card_le_card (Finset.subset_univ C)
    simpa using h
  have hcount := digraph_oriented_safe_set_indegree_bound (Fin 17) digraph_safe17_graph hloop hori 7
    (fun v => (hin v).ge) C hsafe
  have hbound : 7 * C.card ≤ Nat.choose C.card 2 + 2 * (17-C.card) := by
    simpa using hcount
  by_cases hsmall : C.card ≤ 14
  · interval_cases h : C.card <;> norm_num [h, Nat.choose] at hbound
  · have hcard : 15 ≤ C.card := by omega
    obtain ⟨v,hv⟩ := hne
    let U : Finset (Fin 17) := Finset.univ \ C
    have hvU : v ∈ U := by simp [U,hv]
    have hUcard : U.card = 17-C.card := by
      simp [U, Finset.card_sdiff]
    have herase : (U.erase v).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hvU]
      omega
    have hsub : (Finset.univ.filter fun w => digraph_safe17_graph.Adj v w) ⊆
        (C.filter fun w => digraph_safe17_graph.Adj v w) ∪ U.erase v := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      by_cases hwC : w ∈ C
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwC,hadj⟩)
      · have hwu : w ≠ v := by intro h; subst w; exact hloop v hadj
        apply Finset.mem_union_right
        simp [U,hwC,hwu]
    have hcount := Finset.card_le_card hsub
    have hunion := Finset.card_union_le (C.filter fun w => digraph_safe17_graph.Adj v w) (U.erase v)
    have hsafe' := hsafe v hv
    have hd := hout v
    omega
