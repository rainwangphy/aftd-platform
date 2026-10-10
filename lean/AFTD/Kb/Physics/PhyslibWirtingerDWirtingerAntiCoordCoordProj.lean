import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirEqZeroOfClinear
import AFTD.Kb.Physics.PhyslibWirtingerClinearOfHolomorphic
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_coordProj

Topic: classical_mechanics   Node: 34a908db16be

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_coordProj`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`∂̄_I z^J = 0`. The anti-holomorphic coordinate-independence value; also feeds the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` and the conjugate-coordinate value `dWirtingerCoord_conjCoord` (§C).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- `∂̄_I z^J = 0`. The anti-holomorphic coordinate-independence value; also feeds the coordinate-difference rule `dWirtingerAntiCoord_coordDiff` and the conjugate-coordinate value `dWirtingerCoord_conjCoord` (§C). -/
@[simp] lemma Physlib.Wirtinger.dWirtingerAntiCoord_coordProj (I J : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => u J) I = 0 := by
  funext u
  exact dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) J).differentiableAt _)
