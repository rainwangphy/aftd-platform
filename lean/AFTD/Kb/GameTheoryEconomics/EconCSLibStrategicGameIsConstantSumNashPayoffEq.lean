import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# EconCSLib.StrategicGame.IsConstantSum.nash_payoff_eq

Topic: equilibria   Node: f0e40e28d12a

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum.nash_payoff_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a constant-sum game, all Nash equilibria yield the same payoff for player 0. [MSZ Theorem 4.44–4.45]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {U : Type*} in
set_option linter.unusedSectionVars false in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame (Fin 2) U} in
/-- In a constant-sum game, all Nash equilibria yield the same payoff for player 0. [MSZ Theorem 4.44–4.45] -/
theorem EconCSLib.StrategicGame.IsConstantSum.nash_payoff_eq
    {c : U} (hcs : IsConstantSum G c)
    {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 0 = G.payoff τ 0 := by
  have hcross : ∀ j : Fin 2, EconCSLib.StrategicGame.deviate σ 0 (τ 0) j = EconCSLib.StrategicGame.deviate τ 1 (σ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [EconCSLib.StrategicGame.deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) :=
    congr_arg G.payoff (funext hcross)
  have h1 := hσ 0 (τ 0)
  have h2 := hτ 1 (σ 1)
  have hcc := hcs (EconCSLib.StrategicGame.deviate σ 0 (τ 0))
  have hct := hcs τ
  have hge : G.payoff τ 0 ≤ G.payoff σ 0 := by
    have heq0 : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) 0 = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) 0 :=
      congr_fun hpeq 0
    have heq1 : G.payoff (EconCSLib.StrategicGame.deviate σ 0 (τ 0)) 1 = G.payoff (EconCSLib.StrategicGame.deviate τ 1 (σ 1)) 1 :=
      congr_fun hpeq 1
    linarith
  have hcross' : ∀ j : Fin 2, EconCSLib.StrategicGame.deviate τ 0 (σ 0) j = EconCSLib.StrategicGame.deviate σ 1 (τ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [EconCSLib.StrategicGame.deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) :=
    congr_arg G.payoff (funext hcross')
  have h3 := hτ 0 (σ 0)
  have h4 := hσ 1 (τ 1)
  have hcc' := hcs (EconCSLib.StrategicGame.deviate τ 0 (σ 0))
  have hcs' := hcs σ
  have hle : G.payoff σ 0 ≤ G.payoff τ 0 := by
    have heq0' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) 0 = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) 0 :=
      congr_fun hpeq' 0
    have heq1' : G.payoff (EconCSLib.StrategicGame.deviate τ 0 (σ 0)) 1 = G.payoff (EconCSLib.StrategicGame.deviate σ 1 (τ 1)) 1 :=
      congr_fun hpeq' 1
    linarith
  linarith
