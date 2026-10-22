import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodKernel

/-!
# is_c1_k_submod_kernel

Topic: submodular   Node: 7bc3d1c77764

Provenance: original. Related work: arXiv:2610.26677, Lemma 2.1 and proof of Lemma 2.2

A bivariate function H : ℝ → ℝ → ℝ satisfies is_c1_k_submod_kernel if the map (fun p : ℝ × ℝ => H p.1 p.2) is continuously differentiable of class C^1 (ContDiff ℝ 1) and H satisfies is_k_submod_kernel H.
-/

/-- Predicate for a continuously differentiable bivariate kernel satisfying the k-submodularity kernel conditions. -/
def is_c1_k_submod_kernel (H : ℝ → ℝ → ℝ) : Prop := ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧ is_k_submod_kernel H
