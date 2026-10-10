import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_smul

Topic: classical_mechanics   Node: 82e1288ffbc8

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_smul`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Compatibility of `dWirtingerDir` with complex scalar multiplication, `∂_v(c·g) = c·∂_v g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Compatibility of `dWirtingerDir` with complex scalar multiplication, `∂_v(c·g) = c·∂_v g`. -/
lemma Physlib.Wirtinger.dWirtingerDir_smul (c : ℂ) {g : V → ℂ} (hg : DifferentiableAt ℝ g u) (v : V) :
    dWirtingerDir (c • g) v u = c • dWirtingerDir g v u := by
  simp only [dWirtingerDir_apply, fderiv_const_smul hg c, _root_.smul_apply, smul_eq_mul,
    mul_sub, mul_left_comm]
