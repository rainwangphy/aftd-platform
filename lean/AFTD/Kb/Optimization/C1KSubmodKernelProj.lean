import AFTD.Prelude
import AFTD.Kb.Optimization.IsC1KSubmodKernel
import AFTD.Kb.Optimization.KSubmodKernelProj
import AFTD.Kb.Optimization.IsKSubmodKernel

/-!
# c1_k_submod_kernel_proj

Topic: submodular   Node: 7417c12def02

Provenance: helper lemma. arXiv:2610.26677, Lemma 2.1

The first coordinate projection function (fun x _ => x) : ℝ → ℝ → ℝ satisfies is_c1_k_submod_kernel.
-/

/-- The coordinate projection kernel satisfies is_c1_k_submod_kernel (sanity witness). -/
theorem c1_k_submod_kernel_proj : is_c1_k_submod_kernel (fun x _ => x) := ⟨contDiff_fst, k_submod_kernel_proj⟩
