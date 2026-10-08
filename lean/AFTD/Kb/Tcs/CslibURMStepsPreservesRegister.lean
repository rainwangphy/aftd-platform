import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMSteps
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMInstrWritesTo
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMStep
import AFTD.Kb.Tcs.CslibURMStepPreservesRegister
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Steps.preserves_register

Topic: computability   Node: c8857c3a83c5

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Steps.preserves_register`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multi-step execution preserves registers not written by any executed instruction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
variable {p : Program} in
/-- Multi-step execution preserves registers not written by any executed instruction. -/
theorem Cslib.URM.Steps.preserves_register {s s' : State} {r : ℕ}
    (hsteps : Steps p s s')
    (hr : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    s'.regs.read r = s.regs.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep => grind [Step.preserves_register hstep (r := r)]
