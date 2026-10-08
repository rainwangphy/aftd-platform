import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.RSInv
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.RsinvRun
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.RsinvInit
import AFTD.Kb.GameTheoryEconomics.JinvInit
import AFTD.Kb.GameTheoryEconomics.InitStateInjective

/-!
# rsinv_finalState

Topic: matching_markets   Node: 5eb3a2451ac6

Provenance: formalization of a published result. Source: EconCSLib, `rsinv_finalState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

RSInv at finalState.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- RSInv at finalState. -/
lemma rsinv_finalState (w m : Preferences n) :
    RSInv w m (finalState w m) := by
  apply rsinv_run w m (n * n + 1) (initState n) (rsinv_init w m)
  · simp [initState]
  · exact jinv_init m
  · exact initState_injective (n := n)
