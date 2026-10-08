import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMTransitionRelation
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInitCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMHaltCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCompComputer
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMIntermediateCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMFinalCfg
import AFTD.Kb.Tcs.RelationRelatesWithinStepsMap
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMToCompCfgRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMk1
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStep
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMMapToCompCfgRightStep
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
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInhabitedStmt

/-!
# Cslib.Turing.SingleTapeTM.comp_right_relatesWithinSteps

Topic: computability   Node: 5f974bf03976

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.comp_right_relatesWithinSteps`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Simulation for the second phase of the composed computer. When the second machine runs from start to halt, the composed machine runs from Sum.inr tm2.q₀ to halt.
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
/-- Simulation for the second phase of the composed computer. When the second machine runs from start to halt, the composed machine runs from Sum.inr tm2.q₀ to halt. -/
theorem Cslib.Turing.SingleTapeTM.comp_right_relatesWithinSteps (intermediate output : List Symbol) (t : ℕ)
    (htm2 :
      RelatesWithinSteps tm2.TransitionRelation
        (tm2.initCfg intermediate)
        (tm2.haltCfg output)
        t) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      (intermediateCfg tm1 tm2 intermediate)
      (finalCfg tm1 tm2 output)
      t := by
  simp only [intermediateCfg, finalCfg, initCfg, haltCfg] at htm2 ⊢
  refine RelatesWithinSteps.map (toCompCfg_right tm1 tm2) ?_ htm2
  intro a b hab
  grind [map_toCompCfg_right_step tm1 tm2 a]
