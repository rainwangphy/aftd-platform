import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_apply

Topic: classical_mechanics   Node: eef7eee1d498

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real-Fréchet form of `dWirtingerAntiCoord`: `∂̄_I f = (1/2)(∂_x + i · ∂_y) f`, mirror of `dWirtingerCoord_apply` with the sign flip on the imaginary-direction term. Unconditional, as for `dWirtingerCoord_apply`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
/-- Real-Fréchet form of `dWirtingerAntiCoord`: `∂̄_I f = (1/2)(∂_x + i · ∂_y) f`, mirror of `dWirtingerCoord_apply` with the sign flip on the imaginary-direction term. Unconditional, as for `dWirtingerCoord_apply`. -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      + Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerAntiCoord, dWirtingerAntiDir_apply, ← Pi.single_smul', smul_eq_mul, mul_one]
