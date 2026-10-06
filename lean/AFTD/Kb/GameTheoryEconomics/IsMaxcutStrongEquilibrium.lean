import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# is_maxcut_strong_equilibrium

Topic: equilibria   Node: ca7418d38f63

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), Sec. 1

A coloring σ is a strong equilibrium of the Max-k-Cut game if no coalition has a strong deviation from it.
-/

/-- A strong equilibrium of the Max-k-Cut game: a coloring admitting no strong deviation. -/
def is_maxcut_strong_equilibrium {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) : Prop :=
  ∀ (S : Finset V) (τ : V → Fin k), ¬ is_maxcut_strong_deviation G σ S τ
