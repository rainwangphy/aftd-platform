import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveLeftMoveRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveRightMoveLeft
import AFTD.Kb.Tcs.CslibTuringBiTapeSpaceUsedWrite
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Computability.Turing.SingleTape.Cfg

Topic: computability   Node: fba42df883bd

Provenance: formalization of a published result. Source: CSLib, `Cslib.Computability.Turing.SingleTape.Cfg`. Lean proof by Fabrizio Montesi, Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Defs.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Configuration of a single-tape Turing machine.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Configuration of a single-tape Turing machine. -/
@[ext]
structure Cslib.Computability.Turing.SingleTape.Cfg (State Symbol : Type*) where
  /-- The state that the machine is in. -/
  state : State
  /-- Tape of the machine (memory). -/
  tape : Turing.BiTape Symbol
