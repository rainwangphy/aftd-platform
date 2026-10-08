import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNABuchiInterAcc

/-!
# Cslib.Automata.NA.Buchi.interAccept

Topic: automata   Node: 9dd2ca4f7709

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.Buchi.interAccept`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/BuchiInter.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The overall accepting condition of the intersection automaton.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Prod Filter in
variable {Symbol : Type*} {State : Bool → Type*} in
/-- The overall accepting condition of the intersection automaton. -/
@[scoped grind =]
def Cslib.Automata.NA.Buchi.interAccept (acc : (i : Bool) → Set (State i)) : Set ((Π i, State i) × Bool) :=
  interAcc false acc ∪ interAcc true acc
