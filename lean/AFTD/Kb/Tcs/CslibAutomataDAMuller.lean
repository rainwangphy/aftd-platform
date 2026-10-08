import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataDA
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.Automata.DA.Muller

Topic: automata   Node: a13dda86bfbe

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.DA.Muller`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic Muller automaton.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Filter in
variable {State Symbol : Type*} in
/-- Deterministic Muller automaton. -/
structure Cslib.Automata.DA.Muller (State Symbol : Type*) extends DA State Symbol where
  /-- The set of sets of accepting states. -/
  accept : Set (Set State)
