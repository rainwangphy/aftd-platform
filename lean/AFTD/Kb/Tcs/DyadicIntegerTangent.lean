import AFTD.Prelude

/-!
# dyadic_integer_tangent

Topic: combinatorics   Node: e5109591df9e

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

For natural m and t, the rational number m+1-t is at most 2^m divided by 2^t.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem dyadic_integer_tangent (m t : ℕ) :
    (m : ℚ) + 1 - t ≤ (2 : ℚ)^m / 2^t := by
  by_cases htm : t ≤ m
  · have he : (m : ℚ) + 1 - t = (m-t : ℕ) + 1 := by
      rw [Nat.cast_sub htm]
      ring
    rw [he, div_eq_mul_inv, ← pow_sub₀ (2 : ℚ) (by norm_num : (2 : ℚ) ≠ 0) htm]
    have hn : m-t+1 ≤ 2^(m-t) := by
      have : m-t < 2^(m-t) := Nat.lt_two_pow_self
      omega
    exact_mod_cast hn
  · have hn : (m : ℚ) + 1 - t ≤ 0 := by
      have ht : m+1 ≤ t := by omega
      exact_mod_cast (show (m : ℤ) + 1 - t ≤ 0 by omega)
    exact hn.trans (by positivity)
