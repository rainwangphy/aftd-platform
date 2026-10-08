import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotContinuous.independent

Topic: general_equilibrium   Node: 934d9574a6ff

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotContinuous.independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotContinuous.independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotContinuous.independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  simp only [pref, Lottery.mix, stdSimplex.mix]
  constructor
  · intro h
    rcases h with h | ⟨heq, hge⟩
    · left; nlinarith
    · right; constructor <;> nlinarith
  · intro h
    rcases h with h | ⟨heq, hge⟩
    · left; nlinarith
    · right; constructor <;> nlinarith
