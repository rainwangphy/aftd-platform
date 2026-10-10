import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDifferentiableAtDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.differentiableAt_dWirtingerAntiCoord

Topic: classical_mechanics   Node: fcbfe3f87267

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.differentiableAt_dWirtingerAntiCoord`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On a `C²` function the anti-holomorphic coordinate Wirtinger derivative is itself real-differentiable (`DifferentiableAt ℝ (∂̄_J f) u`) — the `d = Pi.single J 1` case of `differentiableAt_dWirtingerAntiDir`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f : (ι → ℂ) → ℂ} {u : (ι → ℂ)} in
/-- On a `C²` function the anti-holomorphic coordinate Wirtinger derivative is itself real-differentiable (`DifferentiableAt ℝ (∂̄_J f) u`) — the `d = Pi.single J 1` case of `differentiableAt_dWirtingerAntiDir`. -/
lemma Physlib.Wirtinger.differentiableAt_dWirtingerAntiCoord (hf2 : ContDiffAt ℝ 2 f u) (J : ι) :
    DifferentiableAt ℝ (fun v => dWirtingerAntiCoord f J v) u :=
  differentiableAt_dWirtingerAntiDir hf2 (Pi.single J 1)
