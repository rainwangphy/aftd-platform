import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInstFintypeState
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCompComputer
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStmt
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMToCompCfgRight
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStep
import AFTD.Kb.Tcs.CslibTuringBiTapeOptionMove
import AFTD.Kb.Tcs.CslibTuringBiTapeWrite
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
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInhabitedStmt

/-!
# Cslib.Turing.SingleTapeTM.map_toCompCfg_right_step

Topic: computability   Node: 22eb6d909aad

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.map_toCompCfg_right_step`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The right converting function commutes with steps of the machines.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.SingleTapeTM in
open Relation in
open Cslib.Turing.BiTape Cslib.Turing.StackTape in
open _root_.Turing in
variable {Symbol : Type} in
variable [Inhabited Symbol] [Fintype Symbol] in
variable (tm1 tm2 : SingleTapeTM Symbol) (cfg1 : tm1.Cfg) (cfg2 : tm2.Cfg) in
/-- The right converting function commutes with steps of the machines. -/
theorem Cslib.Turing.SingleTapeTM.map_toCompCfg_right_step :
    Option.map (toCompCfg_right tm1 tm2) (tm2.step cfg2) =
      (compComputer tm1 tm2).step (toCompCfg_right tm1 tm2 cfg2) := by
  cases cfg2 with
  | mk state BiTape =>
    cases state with
    | none => rfl
    | some q =>
      generalize hM : tm2.tr q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only [compComputer]
      grind [toCompCfg_right, step, compComputer]
