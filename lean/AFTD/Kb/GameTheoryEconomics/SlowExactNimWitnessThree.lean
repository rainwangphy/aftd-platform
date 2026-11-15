import AFTD.Prelude

/-!
# slow_exact_nim_witness_three

Topic: combinatorial_games   Node: 8d453852153a

Provenance: formalization of a published result. Source: arXiv:2611.14546, proof of Corollary 1

For any natural number k, slow_exact_nim_witness_three k is the position on k+1 piles that assigns 1 to pile index 0, 2 to pile index 1, and 3 to all other pile indices.
-/

/-- The witness position (1, 2, 3, ..., 3) for Sprague-Grundy value 3 in slow exact k-Nim with k+1 piles. -/
def slow_exact_nim_witness_three (k : ℕ) : Fin (k + 1) → ℕ := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 3
