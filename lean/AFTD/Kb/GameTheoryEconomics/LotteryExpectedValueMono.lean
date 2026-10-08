import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue

/-!
# Lottery.expectedValue_mono

Topic: general_equilibrium   Node: 609f2e8620ee

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.expectedValue_mono`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected value is monotone: if `f ≤ g` pointwise, then `E[f] ≤ E[g]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
variable {O : Type*} [Fintype O] in
/-- Expected value is monotone: if `f ≤ g` pointwise, then `E[f] ≤ E[g]`. -/
theorem Lottery.expectedValue_mono {L : Lottery 𝕜 O} {f g : O → 𝕜}
    (h : ∀ o, f o ≤ g o) :
    Lottery.expectedValue L f ≤ Lottery.expectedValue L g :=
  wsum_le_wsum L h
