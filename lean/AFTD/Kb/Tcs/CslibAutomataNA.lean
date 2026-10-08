import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Automata.NA

Topic: automata   Node: c79028648420

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nondeterministic automaton extends a `LTS` with a set of initial states.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
/-- A nondeterministic automaton extends a `LTS` with a set of initial states. -/
structure Cslib.Automata.NA (State Symbol : Type*) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State
