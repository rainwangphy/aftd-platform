import AFTD.Prelude
import AFTD.Kb.Tcs.RandomizedOnlineCarpoolingAlg

/-!
# PolyTimeRandomizedOnlineCarpoolingAlg

Topic: online_algorithms   Node: 479a80ca8007

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 3.1, Online carpooling against an oblivious adversary

A polynomial-time randomized online carpooling algorithm extends RandomizedOnlineCarpoolingAlg with a step time complexity function step_time : ℕ → ℕ → ℕ such that both step_time and the coin count num_coins are bounded by polynomials in n + T.
-/

/-- A polynomial-time randomized online carpooling algorithm. -/
structure PolyTimeRandomizedOnlineCarpoolingAlg extends RandomizedOnlineCarpoolingAlg where
  step_time : ℕ → ℕ → ℕ
  step_time_poly : ∃ p : Polynomial ℕ, ∀ n T, step_time n T ≤ p.eval (n + T)
  coins_poly : ∃ p : Polynomial ℕ, ∀ n T, num_coins n T ≤ p.eval (n + T)
