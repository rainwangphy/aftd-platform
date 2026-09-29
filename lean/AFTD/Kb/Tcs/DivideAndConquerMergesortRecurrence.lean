import AFTD.Prelude
import AFTD.Kb.Tcs.DivideAndConquerEqualRootsRecurrence

/-!
# divide_and_conquer_mergesort_recurrence

Topic: algorithms   Node: 77a6cbe516b5

The mergesort recurrence T(k+1) = 2*T(k) + c*2^(k+1) with base cost T(0) = d has exact solution T(k) = d*2^k + c*k*2^k.
-/

/-- Exact closed-form solution to the classic mergesort recurrence on power-of-two input sizes. -/
theorem divide_and_conquer_mergesort_recurrence
    (T : ℕ → ℝ) (c d : ℝ)
    (h0 : T 0 = d)
    (hrec : ∀ k : ℕ, T (k + 1) = 2 * T k + c * 2 ^ (k + 1)) :
    ∀ k : ℕ, T k = d * 2 ^ k + c * (k : ℝ) * 2 ^ k := divide_and_conquer_equal_roots_recurrence T 2 c d h0 hrec
