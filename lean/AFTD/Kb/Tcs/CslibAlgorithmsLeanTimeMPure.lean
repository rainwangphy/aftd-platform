import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeM

/-!
# Cslib.Algorithms.Lean.TimeM.pure

Topic: algorithms   Node: cadf663c766a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.pure`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifts a pure value into a `TimeM` computation with zero time cost. Prefer to use `pure` instead of `TimeM.pure`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Lifts a pure value into a `TimeM` computation with zero time cost. Prefer to use `pure` instead of `TimeM.pure`. -/
protected def Cslib.Algorithms.Lean.TimeM.pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩
