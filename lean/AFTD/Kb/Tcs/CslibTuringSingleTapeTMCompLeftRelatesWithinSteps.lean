import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMTransitionRelation
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInitCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMHaltCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMCompComputer
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMInitialCfg
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMIntermediateCfg
import AFTD.Kb.Tcs.RelationRelatesWithinStepsMap
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMToCompCfgLeft
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStep
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStmt
import AFTD.Kb.Tcs.CslibTuringBiTapeOptionMove
import AFTD.Kb.Tcs.CslibTuringBiTapeWrite
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMMapToCompCfgLeftStep
import AFTD.Kb.Tcs.CslibTuringBiTapeMk1
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
# Cslib.Turing.SingleTapeTM.comp_left_relatesWithinSteps

Topic: computability   Node: 947647ba9145

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.comp_left_relatesWithinSteps`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Simulation for the first phase of the composed computer. When the first machine runs from start to halt, the composed machine runs from start (with Sum.inl state) to Sum.inr tm2.q₀ (the start of the second phase). This takes the same number of steps because the halt transition becomes a transition to the second machine.
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
/-- Simulation for the first phase of the composed computer. When the first machine runs from start to halt, the composed machine runs from start (with Sum.inl state) to Sum.inr tm2.q₀ (the start of the second phase). This takes the same number of steps because the halt transition becomes a transition to the second machine. -/
theorem Cslib.Turing.SingleTapeTM.comp_left_relatesWithinSteps (input intermediate : List Symbol) (t : ℕ)
    (htm1 :
      RelatesWithinSteps tm1.TransitionRelation
        (tm1.initCfg input)
        (tm1.haltCfg intermediate)
        t) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      (initialCfg tm1 tm2 input)
      (intermediateCfg tm1 tm2 intermediate)
      t := by
  simp only [initialCfg, intermediateCfg, initCfg, haltCfg] at htm1 ⊢
  refine RelatesWithinSteps.map (toCompCfg_left tm1 tm2) ?_ htm1
  intro a b hab
  have ha : a.state.isSome := by
    simp only [TransitionRelation, step] at hab
    cases a with | mk state _ => cases state <;> simp_all
  have h1 := map_toCompCfg_left_step tm1 tm2 a ha
  rw [hab, Option.map_some] at h1
  exact h1.symm
