import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStmt
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthNil
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveLeftMoveRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveRightMoveLeft
import AFTD.Kb.Tcs.CslibTuringBiTapeSpaceUsedWrite
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Turing.SingleTapeTM

Topic: computability   Node: c5e7ec86d9ef

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A single-tape Turing machine over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing in
open Relation in
open Cslib.Turing.BiTape Cslib.Turing.StackTape in
open _root_.Turing in
variable {Symbol : Type} in
/-- A single-tape Turing machine over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol). -/
structure Cslib.Turing.SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  (State : Type)
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- Initial state -/
  (q₀ : State)
  /-- Transition function, mapping a state and a head symbol to a `Stmt` to invoke,
  and optionally the new state to transition to afterwards (`none` for halt) -/
  (tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State)
