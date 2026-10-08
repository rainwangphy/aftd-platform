import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor

/-!
# Cslib.Algorithms.Lean.TimeM.instSeqOfAdd

Topic: algorithms   Node: a0bf367ff73e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.instSeqOfAdd`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.instSeqOfAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Algorithms.Lean.TimeM.instSeqOfAdd [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩
