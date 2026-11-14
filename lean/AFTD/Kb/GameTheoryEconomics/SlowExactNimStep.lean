import AFTD.Prelude

/-!
# slow_exact_nim_step

Topic: combinatorial_games   Node: b5950c9824f1

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

Given a natural number n, a position x : Fin n → ℕ on n piles, and a subset of pile indices S : Finset (Fin n), the follower position slow_exact_nim_step x S is the function Fin n → ℕ that maps each index i ∈ S to x i - 1 (using natural number subtraction) and every index i ∉ S to x i.
-/

/-- One move step in slow exact k-Nim on n piles, decrementing coordinates in S. -/
def slow_exact_nim_step {n : ℕ} (x : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ S then x i - 1 else x i
