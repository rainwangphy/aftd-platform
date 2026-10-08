import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMInstPureOfZero

/-!
# Cslib.Algorithms.Lean.TimeM.bind

Topic: algorithms   Node: d30ad7cb271c

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.bind`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sequentially composes two `TimeM` computations, summing their time costs. Prefer to use the `>>=` notation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Sequentially composes two `TimeM` computations, summing their time costs. Prefer to use the `>>=` notation. -/
protected def Cslib.Algorithms.Lean.TimeM.bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩
