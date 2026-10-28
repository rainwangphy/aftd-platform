import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsChordal
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutOp89ExistsOfMaxDegreeLe

/-!
# chordal_maxcut_optimal_strong_equilibrium_of_max_degree_le

Topic: equilibria   Node: f5054901c7ac

Provenance: formalization of a published result. Source: arXiv:2610.04948

For every finite simple chordal graph G whose maximum degree is at most 2k - 1 and every integer k ≥ 3, the unweighted Max-k-Cut game admits an optimal coloring that is a strong equilibrium.
-/

/-- For any finite simple chordal graph with maximum degree at most 2k - 1, the Max-k-Cut game has an optimal strong equilibrium. -/
theorem chordal_maxcut_optimal_strong_equilibrium_of_max_degree_le
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hchord : is_chordal G) (hk : 3 ≤ k) (hdeg : ∀ v, G.degree v ≤ 2 * k - 1) :
    maxcut_has_optimal_strong_equilibrium G k := maxcut_op89_exists_of_max_degree_le G k hk hdeg
