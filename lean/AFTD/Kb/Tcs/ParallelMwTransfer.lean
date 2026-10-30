import AFTD.Prelude

/-!
# parallel_mw_transfer

Topic: combinatorics   Node: 76834be03485

Provenance: formalization of a published result. Source: OP-670

For a natural number n, a function q : Fin n → ℕ, and indices i, j : Fin n, parallel_mw_transfer q i j is the function Fin n → ℕ defined by Function.update (Function.update q i (q i + 1)) j (q j - 1).
-/

/-- The elementary transfer replacing (q_i, q_j) with (q_i + 1, q_j - 1). -/
def parallel_mw_transfer {n : ℕ} (q : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ := Function.update (Function.update q i (q i + 1)) j (q j - 1)
