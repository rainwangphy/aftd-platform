import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataDA
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibFLTSProd

/-!
# Cslib.Automata.DA.prod

Topic: automata   Node: e121b5768567

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.DA.prod`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Prod.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of two deterministic automata.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List in
open scoped Cslib.FLTS in
variable {State1 State2 Symbol : Type*} in
/-- The product of two deterministic automata. -/
@[scoped grind =]
def Cslib.Automata.DA.prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol where
  toFLTS := da1.toFLTS.prod da2.toFLTS
  start := (da1.start, da2.start)
