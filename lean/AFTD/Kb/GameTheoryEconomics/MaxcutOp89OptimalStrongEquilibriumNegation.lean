import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsOptimumRigidity
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsRefutesOfRigidity
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium

/-!
# maxcut_op89_optimal_strong_equilibrium_negation

Topic: equilibria   Node: 5835c0078694

Provenance: original. Related work: arXiv:2610.04948, Section 4 (concluding remarks), Question 2 (OP-89): does every unweighted Max-k-Cut game admit an optimal coloring that is a strong equilibrium? Answered negatively for k = 3 by the pinned twins graph.

It is not true that for every finite type V, simple graph G on V with decidable adjacency, and k ≥ 3, the unweighted Max-k-Cut game on G has an optimal coloring that is a strong equilibrium (the negation of maxcut_op89_optimal_strong_equilibrium_exists); the 182-vertex pinned twins graph with k = 3 is a counterexample.
-/

private instance maxcut_op89_optimal_strong_equilibrium_negation_dec :
    DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph
  infer_instance

theorem maxcut_op89_optimal_strong_equilibrium_negation :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      3 ≤ k → maxcut_has_optimal_strong_equilibrium G k := fun h => maxcut_pinned_twins_refutes_of_rigidity maxcut_pinned_twins_optimum_rigidity
  (h _ maxcut_pinned_twins_graph 3 le_rfl)
