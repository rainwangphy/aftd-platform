import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphEdgeCountLe
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphIndepFreeFour
import AFTD.Kb.Tcs.DigraphSmallOverlapCyclePackingStep
import AFTD.Kb.Tcs.Digraph127RegularIndependenceSmallOverlap

/-!
# digraph_127_four_cycles_under_extremal_and_cycle_criteria

Topic: graphs   Node: a48a048a05b7

Provenance: helper lemma. Proposed exceptional-vertex reduction for OP-110; experiments 12602 and 12603 check the finite arithmetic.

A 7-outregular oriented digraph on 127 vertices with dominated arcs and a cycle in every in-neighborhood contains four disjoint directed cycles, assuming the displayed induced one-, two- and three-cycle criteria and the near-extremal clique-free coloring criterion.
-/

theorem digraph_127_four_cycles_under_extremal_and_cycle_criteria
    (D : Digraph (Fin 127)) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hin : ∀ v, ∃ C : Finset (Fin 127), digraph_directed_cycle_on D C ∧
      ∀ w ∈ C, D.Adj w v)
    (hone : ∀ T : Finset (Fin 127), T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset (Fin 127), C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset (Fin 127), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 127), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset (Fin 127), T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset (Fin 127), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hnear : ∀ (n s : ℕ), 2 ≤ s → 2 * s + 1 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (s + 1) →
        (SimpleGraph.turanGraph n s).edgeFinset.card + 2 ≤ G.edgeFinset.card + n / s →
        G.Colorable s) :
    ∃ c : Fin 4 → Finset (Fin 127), (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)) := by
  classical
  by_contra hno
  have hindep := digraph_common_predecessor_graph_indep_free_four (Fin 127) D hin hno
  have hsmall := digraph_127_regular_independence_small_overlap D hreg hindep
  have hdeg' : ∀ v, 5 + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card := by
    intro v
    rw [hreg v]
  exact hno (digraph_small_overlap_cycle_packing_step (Fin 127) D 3 5 hloop hdeg' hdom
    (by convert hsmall using 4; ext e; simp only [SimpleGraph.mem_edgeFinset]) hthree)
