import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCfgSpaceUsed
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMHaltCfg
import AFTD.Kb.Tcs.CslibTuringBiTapeSpaceUsedMk1
import AFTD.Kb.Tcs.CslibTuringBiTape
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
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStep
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_haltCfg

Topic: computability   Node: f2367de2a932

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_haltCfg`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_haltCfg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.SingleTapeTM in
open Relation in
open Cslib.Turing.BiTape Cslib.Turing.StackTape in
open _root_.Turing in
variable {Symbol : Type} in
variable [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol) in
@[grind =]
lemma Cslib.Turing.SingleTapeTM.Cfg.spaceUsed_haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) :
    (tm.haltCfg s).spaceUsed = max 1 s.length := BiTape.spaceUsed_mk₁ s
