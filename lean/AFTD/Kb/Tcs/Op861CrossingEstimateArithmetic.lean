import AFTD.Prelude

/-!
# op861_crossing_estimate_arithmetic

Topic: graphs   Node: 6e7d9b079a54

Provenance: helper lemma. The arithmetic reduction used for op861_ternary_crossing_pairs_dense.

For real n, k, p and t, if n is at least three, 2k=n+1, t+p=k squared, and 3nt is at most 3k cubed plus n times (nk minus k squared), then n squared is at most 24p.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000

theorem op861_crossing_estimate_arithmetic (n k p t : ℝ)
    (hn : 3 ≤ n) (hk : 2 * k = n + 1)
    (hcount : t + p = k^2)
    (hfourier : 3*n*t ≤ 3*k^3 + n*(n*k-k^2)) :
    n^2 ≤ 24*p := by
  have hnpos : 0 < n := by linarith
  have hk' : k = (n+1)/2 := by linarith
  subst k
  have hcount' : n * (t+p) = n * ((n+1)/2)^2 := by rw [hcount]
  have hpoly : n^3 ≤ (n^2-1)*(n+3) := by nlinarith [sq_nonneg (n-1)]
  have hn3 : n^3 ≤ 24*n*p := by nlinarith [hcount', hfourier, hpoly]
  apply (mul_le_mul_iff_left₀ hnpos).mp
  nlinarith [hn3]
