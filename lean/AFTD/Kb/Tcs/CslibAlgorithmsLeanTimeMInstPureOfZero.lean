import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMPure

/-!
# Cslib.Algorithms.Lean.TimeM.instPureOfZero

Topic: algorithms   Node: 66a874097a27

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.instPureOfZero`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.instPureOfZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Algorithms.Lean.TimeM.instPureOfZero [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure
