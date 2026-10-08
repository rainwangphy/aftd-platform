import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Lottery.expectedValue_const

Topic: general_equilibrium   Node: 49b81c0d73e6

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.expectedValue_const`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected value of a constant is the constant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
variable {O : Type*} [Fintype O] in
/-- Expected value of a constant is the constant. -/
theorem Lottery.expectedValue_const (L : Lottery 𝕜 O) (c : 𝕜) :
    Lottery.expectedValue L (fun _ => c) = c :=
  wsum_const L c
