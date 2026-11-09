import AFTD.Prelude

/-!
# sum_choose_convolution

Topic: combinatorics   Node: d5893d793972

Provenance: helper lemma. arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Lemma 2.5

For natural numbers $d$ and $n$ with $2d - 1 \le n$, the binomial sum $\sum_{j=0}^d \binom{n - (2d-1)}{j} \binom{2d-1}{d-j}$ equals $\binom{n}{d}$.
-/

/-- Binomial convolution identity evaluating the sum of products of binomial coefficients to a single binomial coefficient. -/
theorem sum_choose_convolution (d n : ℕ) (hn : 2 * d - 1 ≤ n) :
    ∑ j ∈ Finset.range (d + 1), (n - (2 * d - 1)).choose j * (2 * d - 1).choose (d - j) =
      n.choose d := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (n - (2 * d - 1)).choose a * (2 * d - 1).choose b) d]
  rw [← Nat.add_choose_eq]
  rw [Nat.sub_add_cancel hn]
