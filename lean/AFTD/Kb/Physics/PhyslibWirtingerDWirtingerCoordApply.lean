import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerCoord_apply

Topic: classical_mechanics   Node: 19628f46156f

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerCoord_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real-Fréchet form of `dWirtingerCoord`: `dWirtingerCoord f I u = (1/2)(∂_x − i · ∂_y) f`, the derivatives along the slot-I real and imaginary coordinate directions. Unconditional — the directional definition makes it definitional (`Complex.I • Pi.single I 1 = Pi.single I Complex.I`); no differentiability hypothesis is needed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
/-- Real-Fréchet form of `dWirtingerCoord`: `dWirtingerCoord f I u = (1/2)(∂_x − i · ∂_y) f`, the derivatives along the slot-I real and imaginary coordinate directions. Unconditional — the directional definition makes it definitional (`Complex.I • Pi.single I 1 = Pi.single I Complex.I`); no differentiability hypothesis is needed. -/
lemma Physlib.Wirtinger.dWirtingerCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      - Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerCoord, dWirtingerDir_apply, ← Pi.single_smul', smul_eq_mul, mul_one]
