import AFTD.Prelude
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# dyadic_integer_tangent_eq_iff

Topic: combinatorics   Node: 67b003c39473

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Equality in the rational dyadic tangent bound occurs exactly at t=m or t+1=m.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem dyadic_integer_tangent_eq_iff (m t : ℕ) :
    (m : ℚ) + 1 - t = (2 : ℚ)^m / 2^t ↔ t = m ∨ t+1 = m := by
  by_cases htm : t ≤ m
  · have he : (m : ℚ) + 1 - t = (m-t : ℕ) + 1 := by
      rw [Nat.cast_sub htm]
      ring
    rw [he, div_eq_mul_inv, ← pow_sub₀ (2 : ℚ) (by norm_num) htm]
    have hc : ((m-t : ℕ) : ℚ) + 1 = (2 : ℚ)^(m-t) ↔
        2^(m-t) = (m-t)+1 := by
      constructor <;> intro h <;> exact_mod_cast h.symm
    rw [hc, two_pow_eq_succ_iff]
    omega
  · have ht : m+1 ≤ t := by omega
    have hn : (m : ℚ) + 1 - t ≤ 0 := by
      exact_mod_cast (show (m : ℤ) + 1 - t ≤ 0 by omega)
    have hp : (0 : ℚ) < 2^m / 2^t := by positivity
    constructor
    · intro h
      linarith
    · omega
