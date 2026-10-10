import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelHiggsVec
import AFTD.Kb.Physics.StandardModelHiggsVecOfReal

/-!
# StandardModel.HiggsVec.ofReal_normSq

Topic: quantum_field_theory   Node: 828d9c81e289

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec.ofReal_normSq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.HiggsVec.ofReal_normSq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.HiggsVec.ofReal_normSq {a : ℝ} (ha : 0 ≤ a) : ‖ofReal a‖ ^ 2 = a := by
  simp [ofReal, PiLp.norm_sq_eq_of_L2, Real.sq_sqrt ha]
