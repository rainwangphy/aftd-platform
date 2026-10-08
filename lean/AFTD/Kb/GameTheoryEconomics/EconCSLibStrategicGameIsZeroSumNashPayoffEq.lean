import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumNeg
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable

/-!
# EconCSLib.StrategicGame.IsZeroSum.nash_payoff_eq

Topic: equilibria   Node: 14f882177d5e

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.nash_payoff_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a zero-sum game, all Nash equilibria yield the same payoff for player 0. [MSZ Theorem 4.44-4.45]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {U : Type*} in
set_option linter.unusedSectionVars false in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame (Fin 2) U} in
/-- In a zero-sum game, all Nash equilibria yield the same payoff for player 0. [MSZ Theorem 4.44-4.45] -/
theorem EconCSLib.StrategicGame.IsZeroSum.nash_payoff_eq
    (hzs : IsZeroSum G) {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 0 = G.payoff τ 0 := by
  -- Cross-profile (τ₀, σ₁) = EconCSLib.StrategicGame.deviate σ 0 (τ 0) = EconCSLib.StrategicGame.deviate τ 1 (σ 1)
  have hcross : ∀ j : Fin 2, EconCSLib.StrategicGame.deviate σ 0 (τ 0) j = EconCSLib.StrategicGame.deviate τ 1 (σ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [EconCSLib.StrategicGame.deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) :=
    congr_arg G.payoff (funext hcross)
  -- σ₀ best-responds to σ₁: payoff(σ) ≥ payoff(τ₀, σ₁)
  have h1 := hσ 0 (τ 0)
  -- τ₁ best-responds to τ₀: payoff(τ,1) ≥ payoff(τ₀, σ₁, 1)
  have h2 := hτ 1 (σ 1)
  -- Zero-sum: convert player 1 inequality to player 0
  have hzc := hzs.neg (EconCSLib.StrategicGame.deviate σ 0 (τ 0))
  have hzt := hzs.neg τ
  -- From h2 + zero-sum: payoff(τ₀,σ₁, 0) ≥ payoff(τ, 0)
  have hge : G.payoff τ 0 ≤ G.payoff σ 0 := by
    -- hzc: payoff(cross,1) = -payoff(cross,0) where cross = EconCSLib.StrategicGame.deviate σ 0 (τ 0)
    -- h2: payoff(EconCSLib.StrategicGame.deviate τ 1 (σ 1),1) ≤ payoff(τ,1)
    -- hpeq: payoff(cross) = payoff(EconCSLib.StrategicGame.deviate τ 1 (σ 1))
    have heq0 : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) 0 = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) 0 :=
      congr_fun hpeq 0
    have heq1 : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) 1 = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) 1 :=
      congr_fun hpeq 1
    -- Now linarith can combine these
    linarith
  -- Symmetric: swap σ and τ
  have hcross' : ∀ j : Fin 2, EconCSLib.StrategicGame.deviate τ 0 (σ 0) j = EconCSLib.StrategicGame.deviate σ 1 (τ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [EconCSLib.StrategicGame.deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) :=
    congr_arg G.payoff (funext hcross')
  have h3 := hτ 0 (σ 0)
  have h4 := hσ 1 (τ 1)
  have hzc' := hzs.neg (EconCSLib.StrategicGame.deviate τ 0 (σ 0))
  have hzs' := hzs.neg σ
  have hle : G.payoff σ 0 ≤ G.payoff τ 0 := by
    have heq0' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) 0 = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) 0 :=
      congr_fun hpeq' 0
    have heq1' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) 1 = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) 1 :=
      congr_fun hpeq' 1
    linarith
  linarith
