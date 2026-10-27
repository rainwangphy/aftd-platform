import AFTD.Prelude

/-!
# two_pow_eq_succ_iff

Topic: combinatorics   Node: fd6da6901113

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

For a natural d, two to the power d equals d+1 exactly when d is zero or one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem two_pow_eq_succ_iff (d : ℕ) : 2^d = d+1 ↔ d = 0 ∨ d = 1 := by
  have hstrict : ∀ e : ℕ, e+3 < 2^(e+2) := by
    intro e
    induction e with
    | zero => norm_num
    | succ e ih =>
      rw [show e+1+2 = (e+2)+1 by omega, pow_succ]
      omega
  by_cases h0 : d = 0
  · simp [h0]
  by_cases h1 : d = 1
  · simp [h1]
  obtain ⟨e, rfl⟩ : ∃ e, d = e+2 := ⟨d-2, by omega⟩
  have := hstrict e
  constructor <;> omega
