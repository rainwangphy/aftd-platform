import AFTD.Prelude

/-!
# LinearPMap.exists_phase_add_im_eq_zero

Topic: quantum_mechanics   Node: ffa5228d577f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.exists_phase_add_im_eq_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.exists_phase_add_im_eq_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
lemma LinearPMap.exists_phase_add_im_eq_zero (z₁ z₂ : ℂ) :
    ∃ θ : ℝ, (exp (I * θ) * z₁ + exp (-I * θ) * z₂).im = 0 := by
  let g : ℝ → ℝ := fun θ ↦ (exp (I * θ) * z₁ + exp (-I * θ) * z₂).im
  have hg : g Real.pi = -g 0 := by simp [g, mul_comm I, exp_neg, add_comm]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g 0) (g Real.pi) := by
    rw [hg]
    rcases le_total (g 0) 0 with h | h
    exacts [Set.mem_uIcc.mpr (.inl ⟨h, by linarith⟩), Set.mem_uIcc.mpr (.inr ⟨by linarith, h⟩)]
  obtain ⟨θ, -, hθ⟩ := intermediate_value_uIcc (by fun_prop : Continuous g).continuousOn hmem
  exact ⟨θ, hθ⟩
