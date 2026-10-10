import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerCoord

Topic: classical_mechanics   Node: baf741ac14cc

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerCoord`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
/-- Holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`. -/
noncomputable def Physlib.Wirtinger.dWirtingerCoord (f : (ι → ℂ) → ℂ) (I : ι) : (ι → ℂ) → ℂ :=
  fun u => dWirtingerDir f (Pi.single I 1) u
