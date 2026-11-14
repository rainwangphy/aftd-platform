import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphIndepFreeFour
import AFTD.Kb.Tcs.DigraphSmallOverlapCyclePackingStep
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFortyFive
import AFTD.Kb.Tcs.Graph126ThreeCliquePartitionOrientedCrossBound
import AFTD.Kb.Tcs.Order

/-!
# digraph_126_four_cycles_under_extremal_and_cycle_criteria

Topic: graphs   Node: ee92b499ac7d

Provenance: helper lemma. Order-126 exclusion for OP-110, using the three-cycle criterion from https://iti.mff.cuni.cz/series/2007/339.pdf and the near-extremal coloring criterion from https://arxiv.org/abs/1409.8665, Theorem 1.1.

A loopless oriented seven-outregular digraph on 126 vertices whose arcs have common predecessors and whose every in-neighborhood contains a directed cycle has four disjoint directed cycles, assuming the displayed induced one-, two- and three-cycle criteria and the stated 126-vertex clique-free three-coloring criterion.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
private instance in833_common_predecessor_decidable {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_126_four_cycles_under_extremal_and_cycle_criteria
    (D : Digraph (Fin 126)) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hin : ∀ v, ∃ C : Finset (Fin 126), digraph_directed_cycle_on D C ∧ ∀ w ∈ C, D.Adj w v)
    (hone : ∀ T : Finset (Fin 126), T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset (Fin 126), C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset (Fin 126), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 126), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset (Fin 126), T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset (Fin 126), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hnear : ∀ (G : SimpleGraph (Fin 126)) [DecidableRel G.Adj],
      G.CliqueFree 4 → 5252 ≤ G.edgeFinset.card → G.Colorable 3)
 :
    ∃ c : Fin 4 → Finset (Fin 126), (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)) := by
  classical
  by_contra hno
  let J := digraph_common_predecessor_graph D
  let H := Jᶜ
  have hindep := digraph_common_predecessor_graph_indep_free_four (Fin 126) D hin hno
  have hfree : H.CliqueFree 4 := by simpa [H,J] using hindep
  have hinc : (∑ v : Fin 126, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) = 2646 := by
    simp [hreg]
    norm_num [Nat.choose]
  have hdeg' : ∀ v, 5 + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card := by
    intro v
    rw [hreg v]
  have hz : 126 ≤ 3 * (2646 - J.edgeFinset.card) := by
    by_contra hh
    have hs : 3 * ((∑ v : Fin 126, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      J.edgeFinset.card) < Fintype.card (Fin 126) := by rw [hinc]; simp only [Fintype.card_fin]; omega
    apply hno
    apply digraph_small_overlap_cycle_packing_step (Fin 126) D 3 5 hloop hdeg' hdom
    · convert hs using 4 <;> ext e <;> simp only [SimpleGraph.mem_edgeFinset] <;> rfl
    · exact hthree
  have hedges : J.edgeFinset.card ≤ 2604 := by omega
  have hdis : Disjoint J.edgeFinset H.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    change Disjoint J Jᶜ
    exact disjoint_compl_right
  have hunion : J.edgeFinset ∪ H.edgeFinset = (⊤ : SimpleGraph (Fin 126)).edgeFinset := by
    rw [← SimpleGraph.edgeFinset_sup]
    change (J ⊔ Jᶜ).edgeFinset = _
    exact SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  have htotal : J.edgeFinset.card + H.edgeFinset.card = 7875 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rw [Nat.choose_two_right]
    norm_num
  have hcolor : H.Colorable 3 := hnear H hfree (by omega)
  obtain ⟨col⟩ := hcolor
  have hclique : ∀ u v, col u = col v → u ≠ v → J.Adj u v := by
    intro u v heq hne
    by_contra h
    have hadj : H.Adj u v := by simp [H, SimpleGraph.compl_adj, hne, h]
    exact (col.map_rel hadj) heq
  have hsubset : ∀ u v, D.Adj u v → J.Adj u v := by
    intro u v huv
    have hne : u ≠ v := by
      intro h
      subst v
      exact hloop u huv
    change u ≠ v ∧ ∃ p, D.Adj p u ∧ D.Adj p v
    exact ⟨hne, hdom u v huv⟩
  have hb := graph_126_three_clique_partition_oriented_cross_bound J D col hclique hsubset hori hedges
  have hc := digraph_three_large_parts_no_four_cycles_cross_ge_forty_five (Fin 126) D col
    hb.1 (by intro v; rw [hreg v]) hone htwo hthree hno
  omega
