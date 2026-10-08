import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Lottery.expectedValue

Topic: general_equilibrium   Node: f6f0d7da4151

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.expectedValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected value of `f` under lottery `L`: `E_L[f] = ∑ o, L(o) · f(o)`. Alias of `wsum` from `Math.Simplex`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- Expected value of `f` under lottery `L`: `E_L[f] = ∑ o, L(o) · f(o)`. Alias of `wsum` from `Math.Simplex`. -/
abbrev Lottery.expectedValue {O : Type*} [Fintype O]
    (L : Lottery 𝕜 O) (f : O → 𝕜) : 𝕜 :=
  wsum L f
