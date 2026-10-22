import AFTD.Prelude

/-!
# subadditive_f_generator

Topic: information   Node: a6c358e1d0fe

Provenance: formalization of a published result. Source: arXiv:2610.21231, equation (4) and Corollary 1

The generator function f associated to parameter α and function s is f(x) = α x log x + ∫_1^x (x - t) (s(t) / t^2) dt.
-/

/-- The f-generator f(x) = α x log x + ∫_1^x (x - t) s(t)/t^2 dt. -/
noncomputable def subadditive_f_generator (α : ℝ) (s : ℝ → ℝ) (x : ℝ) : ℝ := α * x * Real.log x + ∫ t in (1 : ℝ)..x, (x - t) * s t / t ^ 2
