import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumExistsOfCardLe

/-!
# maxcut_op89_exists_of_card_le

Topic: equilibria   Node: a9c36e933ee4

Provenance: formalization of a published result. Source: arXiv:2610.04948 Sec. 3; folklore

For every integer k ≥ 3, every finite simple graph on at most 2k vertices admits an optimal coloring that is a strong equilibrium in the unweighted Max-k-Cut game.
-/

/-- Partial result for OP-89: every graph on at most 2k vertices admits an optimal coloring that is a strong equilibrium. -/
theorem maxcut_op89_exists_of_card_le (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k) (hV : Fintype.card V ≤ 2 * k) : maxcut_has_optimal_strong_equilibrium G k := by
  exact maxcut_strong_equilibrium_exists_of_card_le V G k (by omega) hV
