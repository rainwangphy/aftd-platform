import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.Order

/-!
# digraph_127_regular_independence_small_overlap

Topic: graphs   Node: 7bf5697cfeb8

Provenance: helper lemma. Extremal edge counting for the small-overlap approach to OP-110.

A seven-outregular digraph on 127 vertices whose common-predecessor graph has independence number at most three satisfies the strict 3z overlap condition.
-/

private instance in504_order127_decAdj (D : Digraph (Fin 127)) [DecidableRel D.Adj] :
    DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_127_regular_independence_small_overlap
    (D : Digraph (Fin 127)) [DecidableRel D.Adj]
    (hdeg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hindep : (digraph_common_predecessor_graph D).IndepSetFree 4) :
    3 * ((∑ v : Fin 127, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) < Fintype.card (Fin 127) := by
  classical
  let J := digraph_common_predecessor_graph D
  let H := Jᶜ
  have hfree : H.CliqueFree 4 := by simpa [H,J] using hindep
  have hupper : H.edgeFinset.card ≤ 5376 := by
    have h := SimpleGraph.CliqueFree.card_edgeFinset_le (G := H) (r := 3) hfree
    norm_num at h
    exact h
  have hdis : Disjoint J.edgeFinset H.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    change Disjoint J Jᶜ
    exact disjoint_compl_right
  have hunion : J.edgeFinset ∪ H.edgeFinset = (⊤ : SimpleGraph (Fin 127)).edgeFinset := by
    rw [← SimpleGraph.edgeFinset_sup]
    change (J ⊔ Jᶜ).edgeFinset = _
    exact SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  have htotal : J.edgeFinset.card + H.edgeFinset.card = 8001 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rw [Nat.choose_two_right]
    norm_num
  have hinc : (∑ v : Fin 127, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) = 2667 := by
    simp [hdeg]
    norm_num [Nat.choose]
  change 3 * ((∑ v : Fin 127, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) - J.edgeFinset.card) < 127
  rw [hinc]
  omega
