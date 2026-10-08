import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Automata.NA.Buchi

Topic: automata   Node: 1227f29696f5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.Buchi`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nondeterministic Buchi automaton.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {State Symbol : Type*} in
/-- Nondeterministic Buchi automaton. -/
structure Cslib.Automata.NA.Buchi (State Symbol : Type*) extends NA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State
