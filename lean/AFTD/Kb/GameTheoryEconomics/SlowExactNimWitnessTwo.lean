import AFTD.Prelude

/-!
# slow_exact_nim_witness_two

Topic: combinatorial_games   Node: 754cde8df4fe

Provenance: formalization of a published result. Source: arXiv:2611.14546, proof of Corollary 1

For any natural number k, slow_exact_nim_witness_two k is the position on k+1 piles that assigns 1 to pile indices 0 and 1 and 2 to all other pile indices.
-/

/-- The witness position (1, 1, 2, ..., 2) for Sprague-Grundy value 2 in slow exact k-Nim with k+1 piles. -/
def slow_exact_nim_witness_two (k : ℕ) : Fin (k + 1) → ℕ := fun i => if i.val < 2 then 1 else 2
