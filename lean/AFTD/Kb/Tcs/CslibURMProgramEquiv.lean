import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMEval
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.ProgramEquiv

Topic: computability   Node: 3cdaa64bd7c3

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.ProgramEquiv`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two programs are equivalent if they produce the same result for all inputs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Two programs are equivalent if they produce the same result for all inputs. -/
def Cslib.URM.ProgramEquiv (p q : Program) : Prop :=
  ∀ inputs : List ℕ, eval p inputs = eval q inputs
