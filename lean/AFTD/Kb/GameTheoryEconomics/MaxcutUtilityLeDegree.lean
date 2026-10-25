import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard

/-!
# maxcut_utility_le_degree

Topic: equilibria   Node: e15202623b72

Provenance: helper lemma. step towards maxcut_game_strong_equilibrium_exists

A player's utility in the Max-k-Cut game never exceeds its degree: the neighbours cut away by v form a subset of the neighbours of v.
-/

/-- The utility of v is at most the degree of v. -/
theorem maxcut_utility_le_degree {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (v : V) : maxcut_utility G σ v ≤ G.degree v := by
  have := maxcut_utility_add_monochromatic_card G σ v
  omega
