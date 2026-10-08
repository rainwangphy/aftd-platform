import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMStateIsHalted
import AFTD.Kb.Tcs.CslibURMInstr

/-!
# Cslib.URM.State.instDecidableIsHalted

Topic: computability   Node: 01072c948124

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.instDecidableIsHalted`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.URM.State.instDecidableIsHalted
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.URM.State.instDecidableIsHalted (s : State) (p : Program) : Decidable (s.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ s.pc))
