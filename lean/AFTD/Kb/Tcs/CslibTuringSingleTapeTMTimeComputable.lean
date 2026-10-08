import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMOutputsWithinTime
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.RelationRelatesInStepsZeroIff
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZeroIff
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
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStep
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInhabitedStmt
import AFTD.Kb.Tcs.CslibTuringStackTapeLength

/-!
# Cslib.Turing.SingleTapeTM.TimeComputable

Topic: computability   Node: 450efdfceb61

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.TimeComputable`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Turing machine + a time function + a proof it outputs `f` in at most `time(input.length)` steps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.SingleTapeTM in
open Relation in
open Cslib.Turing.BiTape Cslib.Turing.StackTape in
open _root_.Turing in
variable {Symbol : Type} in
variable [Inhabited Symbol] [Fintype Symbol] in
/-- A Turing machine + a time function + a proof it outputs `f` in at most `time(input.length)` steps. -/
structure Cslib.Turing.SingleTapeTM.TimeComputable (f : List Symbol → List Symbol) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM Symbol
  /-- a bound on runtime -/
  timeBound : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `timeBound(input.length)` steps -/
  outputsFunInTime (a) : tm.OutputsWithinTime a (f a) (timeBound a.length)
