import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataDA
import AFTD.Kb.Tcs.CslibFLTSMtr
import AFTD.Kb.Tcs.CslibAutomataDAProd
import AFTD.Kb.Tcs.CslibFLTSProdMtrEq
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.Automata.DA.prod_mtr_eq

Topic: automata   Node: 3acd214acdcd

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.DA.prod_mtr_eq`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Prod.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is reachable by the product automaton iff its components are reachable by the respective automaton components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List in
open scoped Cslib.FLTS in
variable {State1 State2 Symbol : Type*} in
/-- A state is reachable by the product automaton iff its components are reachable by the respective automaton components. -/
@[simp, scoped grind =]
theorem Cslib.Automata.DA.prod_mtr_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (s : State1 × State2) (xs : List Symbol) :
    (da1.prod da2).mtr s xs = (da1.mtr s.fst xs, da2.mtr s.snd xs) :=
  FLTS.prod_mtr_eq da1.toFLTS da2.toFLTS s xs
