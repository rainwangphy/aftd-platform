import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.sure_thing_principle

Topic: general_equilibrium   Node: f0032d7fb5e2

Provenance: formalization of a published result. Source: EconCSLib, `VNM.sure_thing_principle`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**The Sure-Thing Principle** [MSZ Ex 2.12]: The common lottery in a mixture does not affect strict preference. If Independence holds, then `[α L₁, (1-α) L₃] ≻ [α L₂, (1-α) L₃]` iff `[α L₁, (1-α) L₄] ≻ [α L₂, (1-α) L₄]` for any lotteries `L₁, L₂, L₃, L₄` and `α ∈ [0,1]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {O : Type*} [Fintype O] in
/-- **The Sure-Thing Principle** [MSZ Ex 2.12]: The common lottery in a mixture does not affect strict preference. If Independence holds, then `[α L₁, (1-α) L₃] ≻ [α L₂, (1-α) L₃]` iff `[α L₁, (1-α) L₄] ≻ [α L₂, (1-α) L₄]` for any lotteries `L₁, L₂, L₃, L₄` and `α ∈ [0,1]`. -/
theorem VNM.sure_thing_principle
    {pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop}
    (hind : Independence pref)
    (L₁ L₂ L₃ L₄ : Lottery 𝕜 O)
    (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    strict pref (Lottery.mix α hα₀ hα₁ L₁ L₃) (Lottery.mix α hα₀ hα₁ L₂ L₃) ↔
    strict pref (Lottery.mix α hα₀ hα₁ L₁ L₄) (Lottery.mix α hα₀ hα₁ L₂ L₄) := by
  rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
  · -- α = 0: both mixes collapse to L₃ (resp. L₄); strict X X is false
    have h₃ : Lottery.mix 0 hα₀ hα₁ L₁ L₃ = Lottery.mix 0 hα₀ hα₁ L₂ L₃ :=
      Subtype.ext (funext fun i => by simp [Lottery.mix, stdSimplex.mix])
    have h₄ : Lottery.mix 0 hα₀ hα₁ L₁ L₄ = Lottery.mix 0 hα₀ hα₁ L₂ L₄ :=
      Subtype.ext (funext fun i => by simp [Lottery.mix, stdSimplex.mix])
    simp only [strict, h₃, h₄, and_not_self_iff]
  · -- α > 0: Independence factors out the common lottery
    constructor <;> intro ⟨h₁, h₂⟩ <;> [
      exact ⟨(hind L₁ L₂ L₄ α hα_pos hα₁).mp ((hind L₁ L₂ L₃ α hα_pos hα₁).mpr h₁),
             fun h => h₂ ((hind L₂ L₁ L₃ α hα_pos hα₁).mp ((hind L₂ L₁ L₄ α hα_pos hα₁).mpr h))⟩;
      exact ⟨(hind L₁ L₂ L₃ α hα_pos hα₁).mp ((hind L₁ L₂ L₄ α hα_pos hα₁).mpr h₁),
             fun h => h₂ ((hind L₂ L₁ L₄ α hα_pos hα₁).mp ((hind L₂ L₁ L₃ α hα_pos hα₁).mpr h))⟩
    ]
