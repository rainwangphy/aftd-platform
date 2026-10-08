import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.GameTheoryEconomics.LotteryPure
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# VNM.NotContinuous.not_continuous

Topic: general_equilibrium   Node: 3a746314b21d

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotContinuous.not_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotContinuous.not_continuous
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotContinuous.not_continuous : ¬ Continuity pref := by
  intro h
  -- Use pure outcomes: A₀ ≿ A₁ ≿ A₂ in lex order
  have h12 : pref (Lottery.pure (𝕜 := ℚ) (0 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)) := by
    simp only [pref, Lottery.pure]; left; decide
  have h23 : pref (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (2 : Fin 3)) := by
    simp only [pref, Lottery.pure]; right; constructor <;> decide
  obtain ⟨θ, hθ₀, hθ₁, hfwd, hbwd⟩ := h _ _ _ h12 h23
  -- mix θ (pure 0) (pure 2) has val 0 = θ, val 1 = 0
  -- pure 1 has val 0 = 0, val 1 = 1
  -- hbwd : pref (mix θ _ _ (pure 0) (pure 2)) (pure 1)
  --       = (θ > 0 ∨ (θ = 0 ∧ 0 ≥ 1))
  -- mix θ (pure 0) (pure 2) has val 0 = θ, val 1 = 0
  -- pure 1 has val 0 = 0, val 1 = 1
  have mix0 : (Lottery.mix θ hθ₀ hθ₁ (Lottery.pure (𝕜 := ℚ) (0 : Fin 3))
    (Lottery.pure (2 : Fin 3))).val (0 : Fin 3) = θ := by
    simp [Lottery.mix, stdSimplex.mix, Lottery.pure]
  have mix1 : (Lottery.mix θ hθ₀ hθ₁ (Lottery.pure (𝕜 := ℚ) (0 : Fin 3))
    (Lottery.pure (2 : Fin 3))).val (1 : Fin 3) = 0 := by
    simp [Lottery.mix, stdSimplex.mix, Lottery.pure]
  have p1_0 : (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)).val (0 : Fin 3) = 0 := by
    simp [Lottery.pure]
  have p1_1 : (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)).val (1 : Fin 3) = 1 := by
    simp [Lottery.pure]
  simp only [pref, mix0, mix1, p1_0, p1_1] at hfwd hbwd
  -- hbwd : θ > 0 ∨ (θ = 0 ∧ 0 ≥ 1)
  -- hfwd : 0 > θ ∨ (0 = θ ∧ 1 ≥ 0)
  rcases hbwd with h | ⟨h₁, h₂⟩
  · rcases hfwd with h' | ⟨h', _⟩ <;> linarith
  · linarith
