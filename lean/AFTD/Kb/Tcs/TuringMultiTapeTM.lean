import AFTD.Prelude
import AFTD.Kb.Tcs.TuringTransitionOut

/-!
# Turing.MultiTapeTM

Topic: computability   Node: 981b0396d602

Provenance: formalization of a published result. Source: CSLib, `Turing.MultiTapeTM`. Lean proof by Christian Reitwiessner, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean (Copyright (c) 2026 Christian Reitwiessner. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol). Note that it is not required that `Symbol` or `State` are finite to keep the definition more general. The restriction will be introduced once we start talking about computability by Turing machines in general.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
variable {k : ℕ} {State Symbol : Type*} in
/-- A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol). Note that it is not required that `Symbol` or `State` are finite to keep the definition more general. The restriction will be introduced once we start talking about computability by Turing machines in general. -/
structure Turing.MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    TransitionOut k Symbol State
