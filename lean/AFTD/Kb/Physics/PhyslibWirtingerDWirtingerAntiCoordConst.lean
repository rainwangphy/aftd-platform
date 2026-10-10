import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_const

Topic: classical_mechanics   Node: 70c3b7f7ab8a

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_const`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Constants have zero anti-holomorphic coordinate derivative: `∂̄_I c = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Constants have zero anti-holomorphic coordinate derivative: `∂̄_I c = 0`. -/
@[simp] lemma Physlib.Wirtinger.dWirtingerAntiCoord_const (c : ℂ) (I : ι) :
    dWirtingerAntiCoord (fun _ : (ι → ℂ) => c) I = 0 := by
  funext u; exact dWirtingerAntiDir_const c (Pi.single I 1) u
