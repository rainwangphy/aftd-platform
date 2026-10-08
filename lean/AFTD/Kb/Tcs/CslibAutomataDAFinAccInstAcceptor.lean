import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataAcceptor
import AFTD.Kb.Tcs.CslibAutomataDAFinAcc
import AFTD.Kb.Tcs.CslibFLTSMtr
import AFTD.Kb.Tcs.CslibAutomataDA
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.Automata.DA.FinAcc.instAcceptor

Topic: automata   Node: 336475e86d92

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.DA.FinAcc.instAcceptor`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `DA.FinAcc` accepts a string if its multistep transition function maps the start state and the string to an accept state. This is the standard string recognition performed by DFAs in the literature.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Filter in
open scoped Cslib.FLTS in
variable {State Symbol : Type*} in
/-- A `DA.FinAcc` accepts a string if its multistep transition function maps the start state and the string to an accept state. This is the standard string recognition performed by DFAs in the literature. -/
@[simp, scoped grind =]
instance Cslib.Automata.DA.FinAcc.instAcceptor : Acceptor (DA.FinAcc State Symbol) Symbol where
  Accepts (a : DA.FinAcc State Symbol) (xs : List Symbol) :=
    a.mtr a.start xs ∈ a.accept
