import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsExactPotential
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# EconCSLib.StrategicGame.IsExactPotential.maximizer_is_nash

Topic: equilibria   Node: ddb8cd136880

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsExactPotential.maximizer_is_nash`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/PotentialGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A profile maximizing an exact potential is a Nash equilibrium.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] in
open EconCSLib.StrategicGame in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame N U} in
set_option linter.unusedSectionVars false in
/-- A profile maximizing an exact potential is a Nash equilibrium. -/
theorem EconCSLib.StrategicGame.IsExactPotential.maximizer_is_nash {Φ : G.Profile → U}
    (hΦ : IsExactPotential G Φ) {σ : G.Profile}
    (hmax : ∀ τ : G.Profile, Φ σ ≥ Φ τ) :
    IsNashEquilibrium G σ := by
  intro i s'
  -- Need: payoff(EconCSLib.StrategicGame.deviate σ i s', i) ≤ payoff(σ, i)
  -- By exact potential: payoff(dev) - payoff(σ) = Φ(dev) - Φ(σ)
  have h := hΦ i σ s'
  -- h : payoff(dev) - payoff(σ) = Φ(dev) - Φ(σ)
  -- hmax : Φ(σ) ≥ Φ(dev), i.e., Φ(dev) - Φ(σ) ≤ 0
  have hle : Φ (EconCSLib.StrategicGame.deviate σ i s') - Φ σ ≤ 0 := sub_nonpos.mpr (hmax _)
  -- So payoff(dev) - payoff(σ) ≤ 0, i.e., payoff(dev) ≤ payoff(σ)
  linarith
