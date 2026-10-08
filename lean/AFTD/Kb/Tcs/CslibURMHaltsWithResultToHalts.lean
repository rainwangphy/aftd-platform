import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMHaltsWithResult
import AFTD.Kb.Tcs.CslibURMHalts
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMStateInit
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMRegsOutput
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.HaltsWithResult.toHalts

Topic: computability   Node: 48b1daa46317

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.HaltsWithResult.toHalts`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If a program halts with a result, it halts.
-/

set_option quotPrecheck false
open Cslib Cslib.URM
local notation:50 p " ↓ " inputs:51 => Halts p inputs
local notation:50 p " ↑ " inputs:51 => Diverges p inputs
local notation:50 p " ↓ " inputs:51 " ≫ " result:51 => HaltsWithResult p inputs result

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.URM in
variable (p : Program) in
variable {p : Program} in
/-- If a program halts with a result, it halts. -/
theorem Cslib.URM.HaltsWithResult.toHalts {inputs : List ℕ} {result : ℕ}
    (h : p ↓ inputs ≫ result) : p ↓ inputs :=
  let ⟨s, hsteps, hhalted, _⟩ := h
  ⟨s, hsteps, hhalted⟩
