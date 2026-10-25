import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.Tcs.V

/-!
# maxcut_utility_add_monochromatic_card

Topic: equilibria   Node: 07af5f3adb34

Provenance: helper lemma. step towards maxcut_game_strong_equilibrium_exists

A player's utility plus the number of its neighbours sharing its colour equals its degree.
-/

/-- Utility plus monochromatic neighbour count equals degree. -/
theorem maxcut_utility_add_monochromatic_card {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (v : V) : maxcut_utility G σ v + (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have h := (Finset.univ.filter (G.Adj v)).card_filter_add_card_filter_not
    (fun w => σ w ≠ σ v)
  simpa only [Finset.filter_filter, not_not, maxcut_utility] using h
