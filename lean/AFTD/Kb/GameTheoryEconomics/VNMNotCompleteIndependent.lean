import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMNotCompletePref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotComplete.independent

Topic: general_equilibrium   Node: 714889b49058

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotComplete.independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotComplete.independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotComplete.independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  constructor
  · intro h; simp only [pref] at h; subst h; rfl
  · intro h
    simp only [pref] at h
    have hval : L₁.val = L₂.val := funext fun i => by
      have := congr_arg (fun L => L.val i) h
      simp only [Lottery.mix, stdSimplex.mix] at this
      -- this : α * L₁.val i + (1 - α) * N.val i = α * L₂.val i + (1 - α) * N.val i
      -- or a disjunction if simp simplified differently
      nlinarith
    exact Subtype.ext hval
