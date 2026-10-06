import AFTD.Prelude

/-!
# maxcut_utility

Topic: equilibria   Node: 0273fb83899e

Provenance: formalization of a published result. Source: arXiv:2610.04948 (Social Optimality Does Not Imply Coalitional Stability in Unweighted Max-k-Cut Games), Sec. 1 (definition of the game and utilities)

In the unweighted Max-k-Cut game on a finite simple graph G, a coloring σ : V → [k] gives player v the utility u_v(σ) = |{w ∈ N(v) : σ(w) ≠ σ(v)}|.
-/

/-- Utility of player `v` in the unweighted Max-k-Cut game on `G` under the coloring `σ`: the number of neighbours of `v` whose color differs from `v`'s. -/
def maxcut_utility {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (v : V) : ℕ :=
  (Finset.univ.filter fun w => G.Adj v w ∧ σ w ≠ σ v).card
