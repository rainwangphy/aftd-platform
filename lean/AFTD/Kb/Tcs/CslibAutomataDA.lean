import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.Automata.DA

Topic: automata   Node: a89fd14eced8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.DA`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A deterministic automaton extends a `FLTS` with a unique initial state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Filter in
/-- A deterministic automaton extends a `FLTS` with a unique initial state. -/
structure Cslib.Automata.DA (State Symbol : Type*) extends FLTS State Symbol where
  /-- The initial state of the automaton. -/
  start : State
