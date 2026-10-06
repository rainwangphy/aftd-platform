import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_optimal_strong_up_to_degree

Topic: equilibria   Node: 8e2b0cf9bd1b

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), after Corollary 9 (the degree threshold the open question asks about)

For k and D: on every finite simple graph of maximum degree at most D, every optimal coloring of the Max-k-Cut game with k colors is a strong equilibrium.
-/

/-- Every optimal coloring is stable up to degree `D`: on every finite simple graph whose vertex degrees are all at most `D`, every optimal coloring of the Max-k-Cut game is a strong equilibrium. The threshold Δ*(k) of the open problem is the largest such `D`. -/
def maxcut_optimal_strong_up_to_degree (k D : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ D) →
      ∀ σ : V → Fin k, is_maxcut_optimal G σ → is_maxcut_strong_equilibrium G σ
