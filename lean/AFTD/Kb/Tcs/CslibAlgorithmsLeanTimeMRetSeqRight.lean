import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqRightOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqLeftOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstMonadOfAddZero

/-!
# Cslib.Algorithms.Lean.TimeM.ret_seqRight

Topic: algorithms   Node: 992b091e88f1

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.ret_seqRight`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.ret_seqRight
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] theorem Cslib.Algorithms.Lean.TimeM.ret_seqRight {α} (x : TimeM T α) (y : Unit → TimeM T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl
