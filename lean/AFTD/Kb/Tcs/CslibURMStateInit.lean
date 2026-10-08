import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMRegsOfInputs

/-!
# Cslib.URM.State.init

Topic: computability   Node: 016bc36a0339

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.State.init`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Initial state for a program with given inputs. The program counter starts at 0, and inputs are loaded into registers 0, 1, ....
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Initial state for a program with given inputs. The program counter starts at 0, and inputs are loaded into registers 0, 1, .... -/
@[scoped grind =]
def Cslib.URM.State.init (inputs : List ℕ) : State := ⟨0, Regs.ofInputs inputs⟩
