import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsOptimumRigidity
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsNotColorableThree
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsRefutesOfRigidity
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium

/-!
# maxcut_op89_residual_exists_negation

Topic: equilibria   Node: c9352902de7b

Provenance: original. Related work: arXiv:2610.04948, Section 4 (concluding remarks), Question 2 (OP-89): does every unweighted Max-k-Cut game admit an optimal coloring that is a strong equilibrium? Refutes the residual case maxcut_op89_residual_exists with the pinned twins graph, k = 3.

The residual case maxcut_op89_residual_exists of OP-89 is false: it is not true that every finite simple graph G with k ≥ 3, at least 2k+2 vertices, not k-colorable and with a vertex of degree at least 2k, has an optimal Max-k-Cut coloring that is a strong equilibrium.
-/

private instance maxcut_op89_residual_exists_negation_dec :
    DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph
  infer_instance

theorem maxcut_op89_residual_exists_negation :
    ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ), 3 ≤ k →
      2 * k + 2 ≤ Fintype.card V → ¬ G.Colorable k → (∃ v, 2 * k ≤ G.degree v) →
      maxcut_has_optimal_strong_equilibrium G k := by
  intro h
  apply maxcut_pinned_twins_refutes_of_rigidity maxcut_pinned_twins_optimum_rigidity
  refine h maxcut_pinned_twins_graph 3 le_rfl ?_ maxcut_pinned_twins_not_colorable_three
    ⟨(.inl 0, 0), ?_⟩
  · norm_num [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  · rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    decide
