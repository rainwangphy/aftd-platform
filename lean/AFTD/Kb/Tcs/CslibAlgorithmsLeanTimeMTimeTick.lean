import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetPure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimePure
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeMap
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqRight
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeqLeft
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMTimeSeq
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMRetTick
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqLeftOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqRightOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstMonadOfAddZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstLawfulMonad

/-!
# Cslib.Algorithms.Lean.TimeM.time_tick

Topic: algorithms   Node: c6ec64b94d4c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.time_tick`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.Algorithms.Lean.TimeM.time_tick
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp, grind =] theorem Cslib.Algorithms.Lean.TimeM.time_tick (c : T') : (tick c).time = c := rfl
