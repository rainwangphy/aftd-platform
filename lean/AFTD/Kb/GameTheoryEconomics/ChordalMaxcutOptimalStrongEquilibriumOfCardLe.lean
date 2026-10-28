import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsChordal
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutOp89ExistsOfCardLeTwoMulAddOne

/-!
# chordal_maxcut_optimal_strong_equilibrium_of_card_le

Topic: equilibria   Node: e67a883aef83

Provenance: formalization of a published result. Source: arXiv:2610.04948

For every finite simple chordal graph G on at most 2k + 1 vertices and every integer k ≥ 3, the unweighted Max-k-Cut game admits an optimal coloring that is a strong equilibrium.
-/

/-- For any finite simple chordal graph on at most 2k + 1 vertices, the Max-k-Cut game has an optimal strong equilibrium. -/
theorem chordal_maxcut_optimal_strong_equilibrium_of_card_le
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hchord : is_chordal G) (hk : 3 ≤ k) (hV : Fintype.card V ≤ 2 * k + 1) :
    maxcut_has_optimal_strong_equilibrium G k := maxcut_op89_exists_of_card_le_two_mul_add_one G k hk hV
