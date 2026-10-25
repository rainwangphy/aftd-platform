import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutOp89ExistsOfMaxDegreeLe

/-!
# maxcut_op89_exists_of_max_degree_five

Topic: equilibria   Node: b7db521b1ea0

Provenance: formalization of a published result. Source: arXiv:2610.04948 Cor. 9

For every integer k ≥ 3 and every finite simple graph G whose maximum degree is at most 5, the unweighted Max-k-Cut game admits an optimal coloring that is a strong equilibrium.
-/

/-- Partial result for OP-89: if the maximum degree is at most 5, then for every k ≥ 3 the Max-k-Cut game admits an optimal coloring that is a strong equilibrium. -/
theorem maxcut_op89_exists_of_max_degree_five {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k) (hdeg : ∀ v, G.degree v ≤ 5) : maxcut_has_optimal_strong_equilibrium G k := by
  apply maxcut_op89_exists_of_max_degree_le G k hk
  intro v
  have : 5 ≤ 2 * k - 1 := by omega
  exact le_trans (hdeg v) this
