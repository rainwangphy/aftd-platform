import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.Continuity

Topic: general_equilibrium   Node: 618998679faa

Provenance: formalization of a published result. Source: EconCSLib, `VNM.Continuity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Continuity** (Archimedean / MSZ Axiom 2.12): for `L₁ ≿ L₂ ≿ L₃`, there exists `θ ∈ [0,1]` such that `L₂ ∼ [θ L₁, (1-θ) L₃]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {O : Type*} [Fintype O] in
/-- **Continuity** (Archimedean / MSZ Axiom 2.12): for `L₁ ≿ L₂ ≿ L₃`, there exists `θ ∈ [0,1]` such that `L₂ ∼ [θ L₁, (1-θ) L₃]`. -/
def VNM.Continuity (pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop) : Prop :=
  ∀ (L₁ L₂ L₃ : Lottery 𝕜 O),
    pref L₁ L₂ → pref L₂ L₃ →
    ∃ (θ : 𝕜) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1),
      indiff pref L₂ (Lottery.mix θ hθ₀ hθ₁ L₁ L₃)
