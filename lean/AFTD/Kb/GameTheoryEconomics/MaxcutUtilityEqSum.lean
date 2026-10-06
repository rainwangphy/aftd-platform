import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_utility_eq_sum

Topic: equilibria   Node: 1a8f68113cdf

Provenance: helper lemma. step towards maxcut_optimal_strong_of_degree_le (arXiv:2610.04948, Corollary 9)

The Max-k-Cut utility of v is the sum over all w of the indicator that w is a neighbour of v with a different color.
-/

theorem maxcut_utility_eq_sum {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) (v : V) :
    maxcut_utility G ρ v = ∑ w, if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 := by
  unfold maxcut_utility; rw [Finset.card_filter]
