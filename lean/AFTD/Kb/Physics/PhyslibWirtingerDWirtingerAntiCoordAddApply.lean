import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirAdd
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_add_apply

Topic: classical_mechanics   Node: d5835d0db899

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_add_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise additivity of the anti-holomorphic coordinate derivative at `u`: `∂̄_I (f + g) = ∂̄_I f + ∂̄_I g`. Used to assemble the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Pointwise additivity of the anti-holomorphic coordinate derivative at `u`: `∂̄_I (f + g) = ∂̄_I f + ∂̄_I g`. Used to assemble the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C). -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_add_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerAntiCoord (f + g) I u = dWirtingerAntiCoord f I u + dWirtingerAntiCoord g I u :=
  dWirtingerAntiDir_add hf hg (Pi.single I 1)
