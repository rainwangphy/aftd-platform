import AFTD.Prelude

/-!
# is_eventual_period

Topic: combinatorial_games   Node: 80ae13094796

Provenance: formalization of a published result. Source: folklore

A positive integer $p$ is an eventual period of a sequence $w : \mathbb{N} \to \text{Bool}$ if there exists $N \in \mathbb{N}$ such that $w(n + p) = w(n)$ for all $n \ge N$.
-/

/-- A positive integer p is an eventual period of a binary sequence w if w repeats with period p from some point onwards. -/
def is_eventual_period (w : ℕ → Bool) (p : ℕ) : Prop := 0 < p ∧ ∃ N : ℕ, ∀ n ≥ N, w (n + p) = w n
