import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivMulApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_mul

Topic: classical_mechanics   Node: f80427daac73

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_mul`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Wirtinger Leibniz rule for `dWirtingerDir`, `∂_v(g·h) = ∂_v g·h + g·∂_v h`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The Wirtinger Leibniz rule for `dWirtingerDir`, `∂_v(g·h) = ∂_v g·h + g·∂_v h`. -/
lemma Physlib.Wirtinger.dWirtingerDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerDir (g * h) v u = dWirtingerDir g v u * h u + g u * dWirtingerDir h v u := by
  simp only [dWirtingerDir_apply, fderiv_mul_apply hg hh]; ring
