import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivMulApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_mul

Topic: classical_mechanics   Node: 83744aa23102

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_mul`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Wirtinger Leibniz rule for `dWirtingerAntiDir`, `∂̄_v(g·h) = ∂̄_v g·h + g·∂̄_v h`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The Wirtinger Leibniz rule for `dWirtingerAntiDir`, `∂̄_v(g·h) = ∂̄_v g·h + g·∂̄_v h`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerAntiDir (g * h) v u =
      dWirtingerAntiDir g v u * h u + g u * dWirtingerAntiDir h v u := by
  simp only [dWirtingerAntiDir_apply, fderiv_mul_apply hg hh]; ring
