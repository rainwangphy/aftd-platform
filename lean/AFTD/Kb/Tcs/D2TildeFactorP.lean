import AFTD.Prelude

/-!
# d2_tilde_factor_p

Topic: combinatorics   Node: e28bc491d4b9

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

Given a function W : ℝ → ℝ → ℝ, boolean values eps1, eps2 : Bool, and real numbers x1, x2 : ℝ, the factor d2_tilde_factor_p W eps1 eps2 x1 x2 is the integral over y in Set.Icc (0 : ℝ) 1 of (if eps1 then W x1 y else W y x1) * (if eps2 then W x2 y else W y x2).
-/

/-- The marginal factor P_ε(x₁, x₂) integrating over the fiber of v_ε. -/
noncomputable def d2_tilde_factor_p (W : ℝ → ℝ → ℝ) (eps1 eps2 : Bool) (x1 x2 : ℝ) : ℝ := ∫ y in Set.Icc (0 : ℝ) 1,
    (if eps1 then W x1 y else W y x1) * (if eps2 then W x2 y else W y x2)
