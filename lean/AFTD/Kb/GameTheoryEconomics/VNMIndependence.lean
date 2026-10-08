import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.Independence

Topic: general_equilibrium   Node: 094de72b2efa

Provenance: formalization of a published result. Source: EconCSLib, `VNM.Independence`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Independence**: mixing both sides with a common lottery preserves preference. `L₁ ≿ L₂ ↔ [α L₁, (1-α) N] ≿ [α L₂, (1-α) N]` for `α > 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {O : Type*} [Fintype O] in
/-- **Independence**: mixing both sides with a common lottery preserves preference. `L₁ ≿ L₂ ↔ [α L₁, (1-α) N] ≿ [α L₂, (1-α) N]` for `α > 0`. -/
def VNM.Independence (pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop) : Prop :=
  ∀ (L₁ L₂ N : Lottery 𝕜 O) (α : 𝕜) (hα₀ : 0 < α) (hα₁ : α ≤ 1),
    pref L₁ L₂ ↔ pref (Lottery.mix α (le_of_lt hα₀) hα₁ L₁ N)
                       (Lottery.mix α (le_of_lt hα₀) hα₁ L₂ N)
