import AFTD.Prelude
import AFTD.Kb.Tcs.D2TildeKernelR
import AFTD.Kb.Tcs.D2TildeFactorP

/-!
# d2_tilde_kernel_r_symm

Topic: combinatorics   Node: b31152d6f563

Provenance: helper lemma. arXiv:2611.15027 Section 5

For every function W : ℝ → ℝ → ℝ and all x1, x2 : ℝ, the kernel d2_tilde_kernel_r W is symmetric: d2_tilde_kernel_r W x1 x2 = d2_tilde_kernel_r W x2 x1.
-/

/-- Symmetry of the kernel R(x₁, x₂) = R(x₂, x₁). -/
theorem d2_tilde_kernel_r_symm (W : ℝ → ℝ → ℝ) (x1 x2 : ℝ) :
    d2_tilde_kernel_r W x1 x2 = d2_tilde_kernel_r W x2 x1 := by
  have h (eps1 eps2 : Bool) : d2_tilde_factor_p W eps1 eps2 x1 x2 = d2_tilde_factor_p W eps2 eps1 x2 x1 := by
    unfold d2_tilde_factor_p
    simp_rw [mul_comm]
  unfold d2_tilde_kernel_r
  rw [h true true, h true false, h false true, h false false]
  ring
