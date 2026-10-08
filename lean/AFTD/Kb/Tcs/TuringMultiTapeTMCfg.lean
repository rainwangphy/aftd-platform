import AFTD.Prelude
import AFTD.Kb.Tcs.TuringMultiTapeTM

/-!
# Turing.MultiTapeTM.Cfg

Topic: computability   Node: 63f6f315bd0d

Provenance: formalization of a published result. Source: CSLib, `Turing.MultiTapeTM.Cfg`. Lean proof by Christian Reitwiessner, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean (Copyright (c) 2026 Christian Reitwiessner. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The configurations of a Turing machine is relative to the input of the machine and consist of: - an `Option`al state (or none for the halting state), - the position of the input head (shifted by one), - the contents of the work tape, - the positions of the work tape heads.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Turing in
open Relation in
variable {k : ℕ} {State Symbol : Type*} in
variable {tm : MultiTapeTM k Symbol State} in
/-- The configurations of a Turing machine is relative to the input of the machine and consist of: - an `Option`al state (or none for the halting state), - the position of the input head (shifted by one), - the contents of the work tape, - the positions of the work tape heads. -/
@[ext]
structure Turing.MultiTapeTM.Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
deriving Inhabited
