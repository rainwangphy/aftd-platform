import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalStrongOfDegreeLe
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_strong_equilibrium_exists_of_card_le

Topic: equilibria   Node: f40a4cfdc512

Provenance: original. Related work: special case of the existence question of arXiv:2610.04948, Sec. 4 (does every unweighted Max-k-Cut game admit a strong equilibrium?); immediate from that paper's Corollary 9, since a graph on at most 2k vertices has maximum degree at most 2k − 1

For every k ≥ 1 and every finite simple graph on at most 2k vertices, the Max-k-Cut game has an optimal coloring that is a strong equilibrium; in particular, for k ≥ 3, every graph on at most 6 vertices has a strong equilibrium.
-/

theorem maxcut_strong_equilibrium_exists_of_card_le (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) (hV : Fintype.card V ≤ 2 * k) :
    ∃ σ : V → Fin k, is_maxcut_optimal G σ ∧ is_maxcut_strong_equilibrium G σ := by
  have : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  obtain ⟨σ, hσ⟩ := Finite.exists_max (maxcut_welfare G (k := k))
  refine ⟨σ, hσ, maxcut_optimal_strong_of_degree_le k hk V G (fun v => ?_) σ hσ⟩
  have := G.degree_lt_card_verts v
  omega
