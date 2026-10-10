import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffTanh

/-!
# contDiff_top_tanh

Topic: classical_mechanics   Node: 814f2f4a1fcf

Provenance: formalization of a published result. Source: Physlib, `contDiff_top_tanh`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

tanh is infinitely differentiable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- tanh is infinitely differentiable -/
lemma contDiff_top_tanh : ContDiff ℝ ∞ Real.tanh := by
    rw [contDiff_infty]
    apply contDiff_tanh
