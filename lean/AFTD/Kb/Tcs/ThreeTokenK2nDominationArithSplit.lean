import AFTD.Prelude

/-!
# three_token_k2n_domination_arith_split

Topic: graphs   Node: 78e33937e5f1

Provenance: helper lemma. step towards three_token_complete_bipartite_two_exact

For every integer n ≥ 4, (n + 1)^2 / 4 - 2 = (n - 1)^2 / 4 + n - 2 in natural number arithmetic.
-/

/-- The arithmetic expression (n + 1)^2 / 4 - 2 splits as (n - 1)^2 / 4 + n - 2 in Nat integer division. -/
theorem three_token_k2n_domination_arith_split (n : ℕ) (hn : 4 ≤ n) :
    (n + 1)^2 / 4 - 2 = (n - 1)^2 / 4 + n - 2 := by
  have h_sq : (n + 1)^2 = (n - 1)^2 + n * 4 := by
    have h1 : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub h1
    zify
    rw [hcast]
    ring
  have h_div : (n + 1)^2 / 4 = (n - 1)^2 / 4 + n := by
    rw [h_sq]
    exact Nat.add_mul_div_right ((n - 1)^2) n (by decide)
  rw [h_div]
