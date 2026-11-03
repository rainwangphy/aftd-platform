import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumReduceSingleVertexSums
import AFTD.Kb.GameTheoryEconomics.MaxcutOneSumIndecomposableDeletePreconnected
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_reduce_vertex_deletions

Topic: equilibria   Node: 1c646054338d

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence problem in arXiv:2610.04948, Section 4.

Fix k. If every finite graph whose every vertex deletion is preconnected has a strong k-color equilibrium, then every finite graph has a strong k-color equilibrium.
-/

open Finset

theorem maxcut_strong_equilibrium_reduce_vertex_deletions (k : ℕ)
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ o : V, (G.induce ({o}ᶜ : Set V)).Preconnected) →
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  apply maxcut_strong_equilibrium_reduce_single_vertex_sums k
  intro V _ _ G _ hind
  exact hbase V G (maxcut_one_sum_indecomposable_delete_preconnected G hind)
