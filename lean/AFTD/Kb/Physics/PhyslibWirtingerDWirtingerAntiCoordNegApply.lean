import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_neg_apply

Topic: classical_mechanics   Node: 70d6c9908836

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_neg_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise negation rule for the anti-holomorphic coordinate derivative at `u`: `∂̄_I (−f) = −∂̄_I f`. Used with `dWirtingerAntiCoord_add_apply` to assemble the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Pointwise negation rule for the anti-holomorphic coordinate derivative at `u`: `∂̄_I (−f) = −∂̄_I f`. Used with `dWirtingerAntiCoord_add_apply` to assemble the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C). -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord (fun v => -(f v)) I u = -(dWirtingerAntiCoord f I u) :=
  dWirtingerAntiDir_neg f (Pi.single I 1) u
