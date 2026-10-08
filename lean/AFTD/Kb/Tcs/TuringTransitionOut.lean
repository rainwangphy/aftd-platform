import AFTD.Prelude

/-!
# Turing.TransitionOut

Topic: computability   Node: b32fb4ada7c9

Provenance: formalization of a published result. Source: CSLib, `Turing.TransitionOut`. Lean proof by Christian Reitwiessner, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean (Copyright (c) 2026 Christian Reitwiessner. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The output of the transition function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
variable {k : ℕ} {State Symbol : Type*} in
/-- The output of the transition function. -/
structure Turing.TransitionOut (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputMove : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or none to halt. -/
  q' : Option State
