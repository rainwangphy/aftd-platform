import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalStrongOfDegreeLe
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_op89_exists_of_max_degree_le

Topic: equilibria   Node: b1029c32511e

Provenance: formalization of a published result. Source: arXiv:2610.04948 Cor. 9

For every integer k ≥ 3 and every finite simple graph G whose maximum degree is at most 2k - 1, the unweighted Max-k-Cut game admits an optimal coloring that is a strong equilibrium (arXiv:2610.04948, Corollary 9).
-/

/-- Partial result for OP-89: if the maximum degree is at most 2k - 1, then the Max-k-Cut game admits an optimal coloring that is a strong equilibrium. -/
theorem maxcut_op89_exists_of_max_degree_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k) (hdeg : ∀ v, G.degree v ≤ 2 * k - 1) : maxcut_has_optimal_strong_equilibrium G k := by
  have hk1 : 1 ≤ k := by omega
  have : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk1⟩⟩
  obtain ⟨σ, hσ⟩ := Finite.exists_max (maxcut_welfare G (k := k))
  exact ⟨σ, hσ, maxcut_optimal_strong_of_degree_le k hk1 V G hdeg σ hσ⟩
