import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_has_optimal_strong_equilibrium

Topic: equilibria   Node: c85c1186349d

Provenance: formalization of a published result. Source: arXiv:2610.04948 Sec. 4

In the unweighted Max-k-Cut game on a finite simple graph G with k colors, there exists an optimal coloring σ : V → Fin k that is also a strong equilibrium.
-/

/-- A finite simple graph G admits an optimal coloring that is a strong equilibrium in the unweighted Max-k-Cut game. -/
def maxcut_has_optimal_strong_equilibrium {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop := ∃ σ : V → Fin k, is_maxcut_optimal G σ ∧ is_maxcut_strong_equilibrium G σ
