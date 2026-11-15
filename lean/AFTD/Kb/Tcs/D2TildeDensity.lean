import AFTD.Prelude
import AFTD.Kb.Tcs.D2TildeKernelR

/-!
# d2_tilde_density

Topic: combinatorics   Node: ea9c26a13c32

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

Given a function W : ℝ → ℝ → ℝ, the density d2_tilde_density W is defined as the iterated integral ∫ x1 in Set.Icc (0 : ℝ) 1, ∫ x2 in Set.Icc (0 : ℝ) 1, W x1 x2 * d2_tilde_kernel_r W x1 x2.
-/

/-- Continuous homomorphism density t(D̃₂, W) expressed as a double integral. -/
noncomputable def d2_tilde_density (W : ℝ → ℝ → ℝ) : ℝ := ∫ x1 in Set.Icc (0 : ℝ) 1, ∫ x2 in Set.Icc (0 : ℝ) 1, W x1 x2 * d2_tilde_kernel_r W x1 x2
