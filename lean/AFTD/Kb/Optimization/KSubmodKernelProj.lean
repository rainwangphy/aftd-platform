import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodKernel

/-!
# k_submod_kernel_proj

Topic: submodular   Node: 685d7e827b52

Provenance: helper lemma. arXiv:2610.26677, Lemma 2.1

The coordinate projection function (fun x _ => x) : ℝ → ℝ → ℝ satisfies is_k_submod_kernel.
-/

/-- The coordinate projection function satisfies the kernel conditions. -/
theorem k_submod_kernel_proj : is_k_submod_kernel (fun x _ => x) := by
  dsimp [is_k_submod_kernel]
  refine ⟨rfl, zero_lt_one, fun _ _ _ hx1 _ _ => hx1, fun _ _ _ _ hx12 _ _ _ => hx12,
    fun _ _ _ _ _ _ _ _ => le_rfl,
    fun _ _ _ _ _ _ _ _ _ _ => by simp only [deriv_id'', le_refl],
    fun _ _ _ _ _ _ _ _ _ _ => by simp only [deriv_const, le_refl]⟩
