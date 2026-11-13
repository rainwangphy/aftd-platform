import AFTD.Prelude

/-!
# symmetric_power_sum

Topic: algebraic_complexity   Node: fd87c6f5be34

Provenance: formalization of a published result. Source: arXiv:2611.16690, Hilbert's 17th problem for symmetric functions: undecidability and a counterexample, Section 1

The r-th power sum of an n-dimensional real vector x is the sum of (x i)^r over all indices i in Fin n.
-/

/-- The r-th power sum symmetric function of a vector x. -/
def symmetric_power_sum {n : ℕ} (r : ℕ) (x : Fin n → ℝ) : ℝ := ∑ i : Fin n, x i ^ r
