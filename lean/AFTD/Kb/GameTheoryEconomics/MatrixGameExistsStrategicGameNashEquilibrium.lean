import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsMixedNashEq
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEq
import AFTD.Kb.GameTheoryEconomics.MatrixGameExistsMixedNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviateMixed
import AFTD.Kb.GameTheoryEconomics.MatrixGameExpectedPayoffToStrategicGameZero
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGamePureToMixed
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileOne
import AFTD.Kb.GameTheoryEconomics.MatrixGameExpectedPayoffToStrategicGameOne
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumExpectedPayoffAddZero
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.exists_strategic_game_nash_equilibrium

Topic: equilibria   Node: 1e1f724337bb

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.exists_strategic_game_nash_equilibrium`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

**The strategic-game embedding of a finite matrix game admits a mixed Nash equilibrium.** Combines `MatrixGame.exists_mixed_nash_equilibrium` with the profile-expansion bridge lemmas above.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
variable [DecidableEq I] [DecidableEq J] in
/-- **The strategic-game embedding of a finite matrix game admits a mixed Nash equilibrium.** Combines `MatrixGame.exists_mixed_nash_equilibrium` with the profile-expansion bridge lemmas above. -/
theorem MatrixGame.exists_strategic_game_nash_equilibrium :
    ∃ p : EconCSLib.StrategicGame.MixedProfile A.toStrategicGame,
      EconCSLib.StrategicGame.IsMixedNashEq A.toStrategicGame p := by
  classical
  obtain ⟨xx, yy, hxx, hyy⟩ := A.exists_mixed_nash_equilibrium
  refine ⟨A.toMixedProfile xx yy, ?_⟩
  intro who s'
  -- Manually split on who ∈ {0, 1} so the substitution makes `who` literally 0 or 1.
  have hcases : who = 0 ∨ who = 1 := by
    rcases who with ⟨_ | _ | n, hn⟩
    · left; rfl
    · right; rfl
    · omega
  rcases hcases with rfl | rfl
  · -- Player 0 (row): deviating to pure s' ∈ I cannot improve.
    rw [expectedPayoff_toStrategicGame_zero, expectedPayoff_toStrategicGame_zero]
    have hdev0 : (EconCSLib.StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 0 s') 0
                = EconCSLib.StrategicGame.pureToMixed s' := by
      simp only [EconCSLib.StrategicGame.deviateMixed]
      first
        | exact Function.update_self ..
        | exact Function.update_of_ne (by decide) _ _
    have hdev1 : (EconCSLib.StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 0 s') 1
                = yy := by
      simp only [EconCSLib.StrategicGame.deviateMixed]
      first
        | exact Function.update_self ..
        | exact Function.update_of_ne (by decide) _ _
    rw [hdev0, hdev1, toMixedProfile_zero, toMixedProfile_one]
    exact hxx (EconCSLib.StrategicGame.pureToMixed s')
  · -- Player 1 (column): deviating to pure s' ∈ J cannot improve player 1's payoff.
    rw [expectedPayoff_toStrategicGame_one, expectedPayoff_toStrategicGame_one]
    have hdev0 : (EconCSLib.StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 1 s') 0
                = xx := by
      simp only [EconCSLib.StrategicGame.deviateMixed]
      first
        | exact Function.update_self ..
        | exact Function.update_of_ne (by decide) _ _
    have hdev1 : (EconCSLib.StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 1 s') 1
                = EconCSLib.StrategicGame.pureToMixed s' := by
      simp only [EconCSLib.StrategicGame.deviateMixed]
      first
        | exact Function.update_self ..
        | exact Function.update_of_ne (by decide) _ _
    rw [hdev0, hdev1, toMixedProfile_zero, toMixedProfile_one]
    have h := hyy (EconCSLib.StrategicGame.pureToMixed s')
    linarith
