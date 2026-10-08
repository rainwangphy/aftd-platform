import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibComputabilityTuringSingleTapeTrLabel
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Computability.Turing.SingleTape.SingleTapeNTM

Topic: computability   Node: a7957e1cf697

Provenance: formalization of a published result. Source: CSLib, `Cslib.Computability.Turing.SingleTape.SingleTapeNTM`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/NonDeterministic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped with a set of accepting halting states.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Automata in
/-- A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped with a set of accepting halting states. -/
structure Cslib.Computability.Turing.SingleTape.SingleTapeNTM (State Symbol : Type*)
    extends NA State (TrLabel Symbol) where
  /-- The set of accepting states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  accept_halting (hmem : s ∈ accept) : ¬∃ μ s', Tr s μ s'
