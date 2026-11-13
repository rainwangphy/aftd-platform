import AFTD.Prelude

/-!
# step_function_sigma

Topic: algebraic_complexity   Node: 9c1001f41bbd

Provenance: formalization of a published result. Source: arXiv:2611.16690, Hilbert's 17th problem for symmetric functions: undecidability and a counterexample, Proof of Theorem 3.1 (1)

The step function from ℝ to ℤ that maps t to 0 if |t| ≤ 2/3, to 1 if t > 2/3, and to -1 if t < -2/3.
-/

/-- The three-valued step function mapping t to 0 if |t| ≤ 2/3 and to the sign of t otherwise. -/
noncomputable def step_function_sigma (t : ℝ) : ℤ := if |t| ≤ 2 / 3 then 0 else if 0 < t then 1 else -1
