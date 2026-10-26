import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingTermU

/-!
# nonclairvoyant_scheduling_upper_bound

Topic: online_algorithms   Node: b66b8c204c95

Provenance: formalization of a published result. Source: arXiv:2610.29037 Theorem 4.4

The function `nonclairvoyant_scheduling_upper_bound n lam` takes a natural number n and a real number lambda (lam) and returns a real number: if 1 <= n, it returns the maximum value max_{1 <= i <= n} nonclairvoyant_scheduling_term_U n t i over the integer interval {1, ..., n} with t = (n+1)/(n-1) * lam; otherwise (if n = 0), it returns 0.
-/

/-- The upper bound Psi_n(lambda) achieved by Algorithm mTSS for non-clairvoyant scheduling. -/
noncomputable def nonclairvoyant_scheduling_upper_bound (n : ℕ) (lam : ℝ) : ℝ := let t := ((n : ℝ) + 1) / ((n : ℝ) - 1) * lam
  if h : 1 ≤ n then
    (Finset.Icc 1 n).sup' (by simpa using h) (fun i => nonclairvoyant_scheduling_term_U n t i)
  else
    0
