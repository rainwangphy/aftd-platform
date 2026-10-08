import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataAcceptor
import AFTD.Kb.Tcs.CslibAutomataNAFinAcc
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibAutomataAcceptorMemLanguage
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff
import AFTD.Kb.Tcs.CslibAutomataDAFinAccInstAcceptor

/-!
# Cslib.Automata.NA.FinAcc.instAcceptor

Topic: automata   Node: 9ae1a3bed7ab

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.FinAcc.instAcceptor`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

An `NA.FinAcc` accepts a string if there is a multistep transition from a start state to an accept state. This is the standard string recognition performed by NFAs in the literature.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Automata Cslib.Automata.NA in
open Filter in
variable {State Symbol : Type*} in
/-- An `NA.FinAcc` accepts a string if there is a multistep transition from a start state to an accept state. This is the standard string recognition performed by NFAs in the literature. -/
@[simp, grind =]
instance Cslib.Automata.NA.FinAcc.instAcceptor : Acceptor (FinAcc State Symbol) Symbol where
  Accepts (a : FinAcc State Symbol) (xs : List Symbol) :=
    ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.MTr s xs s'
