import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMNotTransitivePref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotTransitive.independent

Topic: general_equilibrium   Node: c2355a8f07e5

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotTransitive.independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotTransitive.independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotTransitive.independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  simp only [pref, Lottery.mix, stdSimplex.mix]
  constructor
  · intro h; rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  · intro h; rcases h with h | h
    · left; nlinarith
    · right; nlinarith
