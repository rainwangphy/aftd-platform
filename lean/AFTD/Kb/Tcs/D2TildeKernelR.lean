import AFTD.Prelude
import AFTD.Kb.Tcs.D2TildeFactorP

/-!
# d2_tilde_kernel_r

Topic: combinatorics   Node: 86404c560203

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

Given a function W : ℝ → ℝ → ℝ and real numbers x1, x2 : ℝ, the kernel d2_tilde_kernel_r W x1 x2 is the product d2_tilde_factor_p W true true x1 x2 * d2_tilde_factor_p W true false x1 x2 * d2_tilde_factor_p W false true x1 x2 * d2_tilde_factor_p W false false x1 x2.
-/

/-- The product kernel R(x₁, x₂) = ∏_ε P_ε(x₁, x₂). -/
noncomputable def d2_tilde_kernel_r (W : ℝ → ℝ → ℝ) (x1 x2 : ℝ) : ℝ := d2_tilde_factor_p W true true x1 x2 *
  d2_tilde_factor_p W true false x1 x2 *
  d2_tilde_factor_p W false true x1 x2 *
  d2_tilde_factor_p W false false x1 x2
