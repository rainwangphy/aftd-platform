import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# is_maxcut_optimal

Topic: equilibria   Node: 296ed3a05720

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), Sec. 1

A coloring σ is optimal if no coloring τ : V → [k] has larger social welfare (equivalently, σ is a maximum k-cut).
-/

/-- An optimal coloring of the Max-k-Cut game: it maximizes social welfare (equivalently the cut value) over all colorings `V → Fin k`. -/
def is_maxcut_optimal {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) : Prop :=
  ∀ τ : V → Fin k, maxcut_welfare G τ ≤ maxcut_welfare G σ
