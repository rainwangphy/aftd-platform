import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsOrdinalPotential
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# EconCSLib.StrategicGame.IsOrdinalPotential.isNash_iff_localMax

Topic: equilibria   Node: 6eae1929062f

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsOrdinalPotential.isNash_iff_localMax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/PotentialGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Nash ↔ local maximizer of ordinal potential.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] in
open EconCSLib.StrategicGame in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame N U} in
set_option linter.unusedSectionVars false in
/-- Nash ↔ local maximizer of ordinal potential. -/
theorem EconCSLib.StrategicGame.IsOrdinalPotential.isNash_iff_localMax {Φ : G.Profile → U}
    (hΦ : IsOrdinalPotential G Φ) {σ : G.Profile} :
    IsNashEquilibrium G σ ↔
    ∀ i (s' : G.strategy i), Φ σ ≥ Φ (EconCSLib.StrategicGame.deviate σ i s') := by
  constructor
  · -- Nash → local max: if payoff doesn't improve, Φ doesn't improve
    intro hN i s'
    by_contra h
    push_neg at h
    -- h: Φ(EconCSLib.StrategicGame.deviate) > Φ(σ), so by ordinal potential: payoff(EconCSLib.StrategicGame.deviate) > payoff(σ)
    have := (hΦ i σ s').mpr h
    -- But Nash says payoff(EconCSLib.StrategicGame.deviate) ≤ payoff(σ)
    exact absurd this (not_lt.mpr (hN i s'))
  · -- Local max → Nash: if Φ doesn't improve, payoff doesn't improve
    intro hmax i s'
    by_contra h
    push_neg at h
    -- h: payoff(EconCSLib.StrategicGame.deviate) > payoff(σ), so by ordinal potential: Φ(EconCSLib.StrategicGame.deviate) > Φ(σ)
    have := (hΦ i σ s').mp h
    -- But local max says Φ(EconCSLib.StrategicGame.deviate) ≤ Φ(σ)
    exact absurd this (not_lt.mpr (hmax i s'))
