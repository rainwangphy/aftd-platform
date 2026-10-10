import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffTanh

/-!
# iteratedDeriv_tanh_differentiable

Topic: classical_mechanics   Node: ed952e124513

Provenance: formalization of a published result. Source: Physlib, `iteratedDeriv_tanh_differentiable`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Iterated derivative for scaled tanh is differentiable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- Iterated derivative for scaled tanh is differentiable -/
lemma iteratedDeriv_tanh_differentiable (n : ℕ) : Differentiable ℝ (iteratedDeriv n tanh) := by
  have h : ContDiff ℝ (n + 1) tanh := by
    apply contDiff_tanh
  apply h.differentiable_iteratedDeriv
  have h' : n < n + 1 := by
    apply Nat.lt_add_one
  norm_cast
