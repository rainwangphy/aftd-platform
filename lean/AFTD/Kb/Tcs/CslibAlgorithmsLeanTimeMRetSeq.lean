import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstBindOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstFunctor
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqLeftOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstSeqRightOfAdd
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstMonadOfAddZero

/-!
# Cslib.Algorithms.Lean.TimeM.ret_seq

Topic: algorithms   Node: 866257ae4ea5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.ret_seq`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.ret_seq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] theorem Cslib.Algorithms.Lean.TimeM.ret_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl
