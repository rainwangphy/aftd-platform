import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd

/-!
# Cslib.Algorithms.Lean.TimeM.instSeqLeftOfAdd

Topic: algorithms   Node: e746a2f52686

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.instSeqLeftOfAdd`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.instSeqLeftOfAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Algorithms.Lean.TimeM.instSeqLeftOfAdd [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩
