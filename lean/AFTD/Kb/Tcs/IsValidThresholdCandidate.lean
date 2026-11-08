import AFTD.Prelude

/-!
# is_valid_threshold_candidate

Topic: information   Node: 33f9bc77e4f3

Provenance: formalization of a published result. Source: arXiv:2610.30613 Remark 6.1

For natural numbers $q$ and $N$, $N$ is a valid candidate threshold for $q$ if $N = 2 * q - 1 \\lor N = 2 * q \\lor N = 2 * q + 1$.
-/

/-- For natural numbers q and N, N is a valid candidate threshold if N = 2*q - 1 ∨ N = 2*q ∨ N = 2*q + 1. -/
def is_valid_threshold_candidate (q N : ℕ) : Prop := N = 2 * q - 1 ∨ N = 2 * q ∨ N = 2 * q + 1
