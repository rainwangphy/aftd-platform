import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityOfProperColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityLeDegree

/-!
# maxcut_optimal_of_proper_coloring

Topic: equilibria   Node: 8a9a43192491

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

A proper k-colouring of a finite simple graph is a maximum k-cut of the Max-k-Cut game: it cuts every edge, so each player's utility equals its full degree, and no colouring can give any player more than its degree.
-/

/-- Any proper k-colouring is an optimal colouring of the Max-k-Cut game. -/
theorem maxcut_optimal_of_proper_coloring {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (h : ∀ v w, G.Adj v w → σ v ≠ σ w) : is_maxcut_optimal G σ := by
  intro τ
  have hdeg : ∀ v, maxcut_utility G σ v = G.degree v :=
    fun v => maxcut_utility_of_proper_coloring G σ h v
  calc maxcut_welfare G τ = ∑ v, maxcut_utility G τ v := rfl
    _ ≤ ∑ v, G.degree v := Finset.sum_le_sum (fun v _ => maxcut_utility_le_degree G τ v)
    _ = ∑ v, maxcut_utility G σ v := Finset.sum_congr rfl (fun v _ => (hdeg v).symm)
    _ = maxcut_welfare G σ := rfl
