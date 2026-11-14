import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphIndepFreeFour
import AFTD.Kb.Tcs.DigraphSmallOverlapCyclePackingStep
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFiftyFour
import AFTD.Kb.Tcs.Graph125ThreeCliquePartitionOrientedCrossBound
import AFTD.Kb.Tcs.Order

/-!
# digraph_125_no_four_cycles_overlap_window

Topic: graphs   Node: f7b0de4fa381

Provenance: helper lemma. Overlap-window reduction for OP-110, using the cycle criteria in https://iti.mff.cuni.cz/series/2007/339.pdf and the coloring criterion in https://arxiv.org/abs/1409.8665, Theorem 1.1.

For a loopless oriented seven-outregular digraph on 125 vertices with dominated arcs, a cycle in each in-neighborhood, and no four disjoint cycles, the common-predecessor overlap is 42 or 43 and its complement is not three-colorable, assuming the displayed induced one-, robust two-, and three-cycle criteria and the stated near-extremal coloring criterion.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
private instance in833_common_predecessor_decidable125 {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_125_no_four_cycles_overlap_window
    (D : Digraph (Fin 125)) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hin : ∀ v, ∃ C : Finset (Fin 125), digraph_directed_cycle_on D C ∧ ∀ w ∈ C, D.Adj w v)
    (hone : ∀ T : Finset (Fin 125), T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset (Fin 125), C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset (Fin 125), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset (Fin 125), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset (Fin 125), T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset (Fin 125), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hnear : ∀ (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj],
      G.CliqueFree 4 → 5169 ≤ G.edgeFinset.card → G.Colorable 3)
    (hno : ¬ ∃ c : Fin 4 → Finset (Fin 125), (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
 :
    let J := digraph_common_predecessor_graph D
    (42 ≤ 2625 - J.edgeFinset.card ∧ 2625 - J.edgeFinset.card ≤ 43) ∧ ¬ Jᶜ.Colorable 3 := by
  classical
  let J := digraph_common_predecessor_graph D
  let H := Jᶜ
  have hindep := digraph_common_predecessor_graph_indep_free_four (Fin 125) D hin hno
  have hfree : H.CliqueFree 4 := by simpa [H,J] using hindep
  have hinc : (∑ v : Fin 125, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) = 2625 := by
    simp [hreg]
    norm_num [Nat.choose]
  have hdeg' : ∀ v, 5 + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card := by
    intro v
    rw [hreg v]
  have hz : 125 ≤ 3 * (2625 - J.edgeFinset.card) := by
    by_contra hh
    have hs : 3 * ((∑ v : Fin 125, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      J.edgeFinset.card) < Fintype.card (Fin 125) := by rw [hinc]; simp only [Fintype.card_fin]; omega
    apply hno
    apply digraph_small_overlap_cycle_packing_step (Fin 125) D 3 5 hloop hdeg' hdom
    · convert hs using 4 <;> ext e <;> simp only [SimpleGraph.mem_edgeFinset] <;> rfl
    · exact hthree
  have hedges : J.edgeFinset.card ≤ 2583 := by omega
  have hsub : ∀ u v, D.Adj u v → J.Adj u v := by
    intro u v huv
    have hne : u ≠ v := by
      intro h
      subst v
      exact hloop u huv
    change u ≠ v ∧ ∃ p, D.Adj p u ∧ D.Adj p v
    exact ⟨hne, hdom u v huv⟩
  have hnotcolor : ¬ H.Colorable 3 := by
    intro hc
    obtain ⟨col⟩ := hc
    have hclique : ∀ u v, col u = col v → u ≠ v → J.Adj u v := by
      intro u v heq hne
      by_contra h
      have hadj : H.Adj u v := by simp [H, SimpleGraph.compl_adj, hne, h]
      exact (col.map_rel hadj) heq
    have hb := graph_125_three_clique_partition_oriented_cross_bound J D col hclique hsub hori hedges
    have hc := digraph_three_large_parts_no_four_cycles_cross_ge_fifty_four (Fin 125) D col
      hb.1 (by intro v; rw [hreg v]) hone htwo hthree hno
    omega
  have hdis : Disjoint J.edgeFinset H.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    change Disjoint J Jᶜ
    exact disjoint_compl_right
  have hunion : J.edgeFinset ∪ H.edgeFinset = (⊤ : SimpleGraph (Fin 125)).edgeFinset := by
    rw [← SimpleGraph.edgeFinset_sup]
    change (J ⊔ Jᶜ).edgeFinset = _
    exact SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  have htotal : J.edgeFinset.card + H.edgeFinset.card = 7750 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rw [Nat.choose_two_right]
    norm_num
  have hupper : H.edgeFinset.card ≤ 5168 := by
    by_contra hh
    exact hnotcolor (hnear H hfree (by omega))
  change (42 ≤ 2625 - J.edgeFinset.card ∧ 2625 - J.edgeFinset.card ≤ 43) ∧ ¬ H.Colorable 3
  exact ⟨⟨by omega, by omega⟩, hnotcolor⟩
