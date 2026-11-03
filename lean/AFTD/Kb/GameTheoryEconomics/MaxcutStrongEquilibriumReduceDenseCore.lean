import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumReduceConnectedCore
import AFTD.Kb.GameTheoryEconomics.MaxcutOp89ExistsOfMaxDegreeLe
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_reduce_dense_core

Topic: equilibria   Node: d395dea3c21c

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence question in arXiv:2610.04948, Section 4.

Fix k at least three. If every finite graph of minimum degree at least k, with preconnected vertex deletions and with some vertex of degree at least 2k, has a strong k-color equilibrium, then every finite graph has a strong k-color equilibrium.
-/

theorem maxcut_strong_equilibrium_reduce_dense_core (k : ℕ) (hk : 3 ≤ k)
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ o : V, (G.induce ({o}ᶜ : Set V)).Preconnected) →
      (∀ v : V, k ≤ G.degree v) → (∃ v : V, 2 * k ≤ G.degree v) →
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  apply maxcut_strong_equilibrium_reduce_connected_core
  intro V _ _ G _ hpre hmin
  by_cases hmax : ∃ v : V, 2 * k ≤ G.degree v
  · exact hbase V G hpre hmin hmax
  · have hdeg : ∀ v : V, G.degree v ≤ 2 * k - 1 := by
      intro v
      have : ¬ (2 * k ≤ G.degree v) := fun h => hmax ⟨v, h⟩
      omega
    have hopt := maxcut_op89_exists_of_max_degree_le G k hk hdeg
    rcases hopt with ⟨σ, _, hse⟩
    exact ⟨σ, hse⟩
