import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerCoordConst

/-!
# Physlib.Wirtinger.dWirtingerCoord_neg_apply

Topic: classical_mechanics   Node: 6feb89103fad

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerCoord_neg_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise negation rule for the holomorphic coordinate derivative at `u`: `∂_I (−f) = −∂_I f`. Used with `dWirtingerCoord_add_apply` to assemble the coordinate-difference rule `dWirtingerCoord_coordDiff` (§C).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Pointwise negation rule for the holomorphic coordinate derivative at `u`: `∂_I (−f) = −∂_I f`. Used with `dWirtingerCoord_add_apply` to assemble the coordinate-difference rule `dWirtingerCoord_coordDiff` (§C). -/
lemma Physlib.Wirtinger.dWirtingerCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord (fun v => -(f v)) I u = -(dWirtingerCoord f I u) :=
  dWirtingerDir_neg f (Pi.single I 1) u
