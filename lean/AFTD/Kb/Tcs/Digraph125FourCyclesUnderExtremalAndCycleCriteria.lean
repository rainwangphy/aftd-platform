import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphIndepFreeFour
import AFTD.Kb.Tcs.Graph125NoncolorableComplementHighDegree
import AFTD.Kb.Tcs.Graph125HighDegreeDeleteComplementColoring
import AFTD.Kb.Tcs.FinsetThreeColorBusiestRecolor
import AFTD.Kb.Tcs.Graph125ThreeCliquesExceptVertexBounds
import AFTD.Kb.Tcs.Graph125ExceptionalThreeCliqueCrossBound
import AFTD.Kb.Tcs.Digraph125NoFourCyclesOverlapWindow
import AFTD.Kb.Tcs.DigraphCommonPredecessorVertexIncidenceBound
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFiftyFour

/-!
# digraph_125_four_cycles_under_extremal_and_cycle_criteria

Topic: graphs   Node: 52eb29b4d7a7

Provenance: helper lemma. Order-125 partial result for OP-110, conditional on the cycle criteria in https://iti.mff.cuni.cz/series/2007/339.pdf and the near-extremal coloring criterion in https://arxiv.org/abs/1409.8665, Theorem 1.1.

A loopless oriented seven-outregular digraph on 125 vertices with dominated arcs and a cycle in every in-neighborhood contains four vertex-disjoint directed cycles, assuming the displayed induced one-, robust two-, and three-cycle criteria and the two stated clique-free three-coloring criteria.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
private instance in833_order125_final_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_125_four_cycles_under_extremal_and_cycle_criteria
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
    (hnear125 : ∀ (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj],
      G.CliqueFree 4 → 5169 ≤ G.edgeFinset.card → G.Colorable 3)
    (hnear124 : ∀ (α : Type) [Fintype α] [DecidableEq α] (H : SimpleGraph α)
      [DecidableRel H.Adj], Fintype.card α = 124 → H.CliqueFree 4 →
      5086 ≤ H.edgeFinset.card → H.Colorable 3) :
    ∃ c : Fin 4 → Finset (Fin 125), (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)) := by
  classical
  by_contra hno
  let J := digraph_common_predecessor_graph D
  have hindep := digraph_common_predecessor_graph_indep_free_four (Fin 125) D hin hno
  have hwin := digraph_125_no_four_cycles_overlap_window D hloop hori hreg hdom hin hone htwo hthree hnear125 hno
  change (42 ≤ 2625 - J.edgeFinset.card ∧ 2625 - J.edgeFinset.card ≤ 43) ∧ ¬ Jᶜ.Colorable 3 at hwin
  have hedges : J.edgeFinset.card ≤ 2583 := by omega
  have hmax : J.edgeFinset.card ≤ 2625 := by omega
  obtain ⟨x,hdegree⟩ := graph_125_noncolorable_complement_high_degree J hindep hwin.2
  obtain ⟨col0,hclique0⟩ := graph_125_high_degree_delete_complement_coloring J x hindep hedges hdegree hnear124
  let O : Finset (Fin 125) := Finset.univ.filter fun w => D.Adj x w
  let I : Finset (Fin 125) := Finset.univ.filter fun w => D.Adj w x
  let M := O ∪ I
  have hnotx : x ∉ M := by simp [M,O,I,hloop]
  obtain ⟨col,hcol,hbalanced⟩ := finset_three_color_busiest_recolor (Fin 125) col0 x M hnotx
  have hclique : ∀ u v, u ≠ x → v ≠ x → col u = col v → u ≠ v → J.Adj u v := by
    intro u v hu hv heq hne
    apply hclique0 u v hu hv _ hne
    calc
      col0 u = col u := (hcol u hu).symm
      _ = col v := heq
      _ = col0 v := hcol v hv
  have ⟨hcapacity,hsizes⟩ := graph_125_three_cliques_except_vertex_bounds J x col hclique hedges
  have hcap : J.degree x + (2625 - J.edgeFinset.card) ≤ 124 := by omega
  have hsub : ∀ u v, D.Adj u v → J.Adj u v := by
    intro u v huv
    have hne : u ≠ v := by
      intro h
      subst v
      exact hloop u huv
    change u ≠ v ∧ ∃ p, D.Adj p u ∧ D.Adj p v
    exact ⟨hne,hdom u v huv⟩
  have hbound : 6 * I.card ≤ J.degree x + (2625 - J.edgeFinset.card) := by
    have h := digraph_common_predecessor_vertex_incidence_bound (Fin 125) D 7 hreg x
    norm_num [Nat.choose] at h
    change 6 * I.card + J.edgeFinset.card ≤ J.degree x + 2625 at h
    omega
  have hdOI : Disjoint O I := by
    apply Finset.disjoint_left.mpr
    intro v hv1 hv2
    exact hori x v (Finset.mem_filter.mp hv1).2 (Finset.mem_filter.mp hv2).2
  have hMcard : M.card = I.card + 7 := by
    rw [Finset.card_union_of_disjoint hdOI]
    have hh : O.card = 7 := hreg x
    omega
  have hfilter : M.filter (fun w => col w = col x) =
      Finset.univ.filter (fun w => col w = col x ∧ (D.Adj x w ∨ D.Adj w x)) := by
    ext w
    simp only [M,O,I,Finset.mem_filter,Finset.mem_union,Finset.mem_univ,true_and]
    exact and_comm
  have hb : (Finset.univ.filter fun w => D.Adj w x).card + 7 ≤
      3 * (Finset.univ.filter fun w => col w = col x ∧ (D.Adj x w ∨ D.Adj w x)).card := by
    rw [← hfilter, ← hMcard]
    exact hbalanced
  have hcross := graph_125_exceptional_three_clique_cross_bound J D x col hclique hsub hori (hreg x) hmax hdegree hwin.1 hbound hcap hb
  have hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card := by
    intro i
    apply le_trans (hsizes i)
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2.2⟩
  have h54 := digraph_three_large_parts_no_four_cycles_cross_ge_fifty_four (Fin 125) D col
    hsize (by intro v; rw [hreg v]) hone htwo hthree hno
  omega
