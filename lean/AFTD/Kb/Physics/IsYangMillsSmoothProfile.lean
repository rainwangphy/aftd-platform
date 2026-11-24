import AFTD.Prelude

/-!
# is_yang_mills_smooth_profile

Topic: classical_fields   Node: 0b126ccd9915

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:137

For a natural number dimension d : ℕ, a function u : ℝ → ℝ, and a real parameter a : ℝ, is_yang_mills_smooth_profile d u a asserts that u is smooth on [0, 1] (ContDiffOn ℝ ⊤ u (Set.Icc 0 1)), u satisfies the Yang-Mills ODE y^2 * (1 - y^2) * iteratedDerivWithin 2 u (Set.Icc 0 1) y + ((d - 3 : ℝ) * y - 2 * y^3) * derivWithin u (Set.Icc 0 1) y + (d - 2 : ℝ) * u y * (1 - (u y)^2) = 0 for all y in Set.Ioo 0 1, there exists y in Set.Icc (0 : ℝ) 1 such that u y ≠ 1, u 0 = 1, derivWithin u (Set.Icc 0 1) 0 = 0, and a = - iteratedDerivWithin 2 u (Set.Icc 0 1) 0 / 2.
-/

/-- Predicate that u is a nonconstant smooth solution on [0,1] of the Yang-Mills profile ODE with shooting parameter a. -/
def is_yang_mills_smooth_profile (d : ℕ) (u : ℝ → ℝ) (a : ℝ) : Prop := ContDiffOn ℝ ⊤ u (Set.Icc 0 1) ∧
  (∀ y ∈ Set.Ioo 0 1, y^2 * (1 - y^2) * iteratedDerivWithin 2 u (Set.Icc 0 1) y +
    ((d - 3 : ℝ) * y - 2 * y^3) * derivWithin u (Set.Icc 0 1) y +
    (d - 2 : ℝ) * u y * (1 - (u y)^2) = 0) ∧
  (∃ y ∈ Set.Icc (0 : ℝ) 1, u y ≠ 1) ∧
  u 0 = 1 ∧
  derivWithin u (Set.Icc 0 1) 0 = 0 ∧
  a = - iteratedDerivWithin 2 u (Set.Icc 0 1) 0 / 2
