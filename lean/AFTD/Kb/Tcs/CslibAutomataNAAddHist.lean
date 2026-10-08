import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Automata.NA.addHist

Topic: automata   Node: 0170659a72b9

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.addHist`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Hist.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The construction of adding a history state. Note that `start'` can depend on the initial value of the original state and `tr'` can depend on the new value of the original state. So there is no loss of generality in their being functions, rather than relations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Prod in
variable {Symbol State Hist : Type*} in
/-- The construction of adding a history state. Note that `start'` can depend on the initial value of the original state and `tr'` can depend on the new value of the original state. So there is no loss of generality in their being functions, rather than relations. -/
@[scoped grind =]
def Cslib.Automata.NA.addHist (na : NA State Symbol) (start' : State → Hist)
    (tr' : State × Hist → Symbol → State → Hist) : NA (State × Hist) Symbol where
  Tr s x t := na.Tr s.fst x t.fst ∧ tr' s x t.fst = t.snd
  start := { s | s.fst ∈ na.start ∧ start' s.fst = s.snd }
