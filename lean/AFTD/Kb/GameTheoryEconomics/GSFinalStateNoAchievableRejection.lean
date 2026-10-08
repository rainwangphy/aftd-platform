import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSDaRunNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.HoldinvInit
import AFTD.Kb.GameTheoryEconomics.InitStateInjective
import AFTD.Kb.GameTheoryEconomics.GSInitStateNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.finalState_NoAchievableRejection

Topic: matching_markets   Node: 19a52d0eb0e6

Provenance: formalization of a published result. Source: EconCSLib, `GS.finalState_NoAchievableRejection`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The invariant holds at `finalState`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- The invariant holds at `finalState`. -/
lemma GS.finalState_NoAchievableRejection :
    NoAchievableRejection w m (finalState w m) :=
  daRun_NoAchievableRejection w m (n * n + 1) (initState n)
    (holdinv_init m) (initState_injective (n := n))
    (initState_NoAchievableRejection w m)
