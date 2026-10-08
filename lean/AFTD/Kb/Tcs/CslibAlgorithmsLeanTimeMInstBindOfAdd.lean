import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMBind
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero

/-!
# Cslib.Algorithms.Lean.TimeM.instBindOfAdd

Topic: algorithms   Node: bfded84232c5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.instBindOfAdd`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.instBindOfAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Algorithms.Lean.TimeM.instBindOfAdd [Add T] : Bind (TimeM T) where
  bind := TimeM.bind
