import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_welfare

Topic: equilibria   Node: 59254a1beb1c

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), Sec. 1

The social welfare of a coloring σ in the Max-k-Cut game: the sum over all players v of u_v(σ), equal to twice the cut value.
-/

/-- Social welfare of a coloring in the unweighted Max-k-Cut game: the sum of the players' utilities, which is twice the number of bichromatic edges. -/
def maxcut_welfare {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) : ℕ :=
  ∑ v, maxcut_utility G σ v
