import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.GSIsAchievable
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.initState_NoAchievableRejection

Topic: matching_markets   Node: 6d6d704cc906

Provenance: formalization of a published result. Source: EconCSLib, `GS.initState_NoAchievableRejection`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The invariant holds vacuously at `initState`: no man has proposed yet.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- The invariant holds vacuously at `initState`: no man has proposed yet. -/
lemma GS.initState_NoAchievableRejection :
    NoAchievableRejection w m (initState n) := by
  intro j wj _ h
  simp [initState] at h
