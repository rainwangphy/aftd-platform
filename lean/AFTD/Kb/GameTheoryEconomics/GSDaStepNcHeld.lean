import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# GS.daStep_nc_held

Topic: matching_markets   Node: 34b49a8eb3a7

Provenance: formalization of a published result. Source: EconCSLib, `GS.daStep_nc_held`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.daStep_nc_held
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
lemma GS.daStep_nc_held {n : ℕ} {w m : Preferences n} {s : DAState n} {i : Fin n}
    (hi : isFree s i = false) : (daStep w m s).nextChoice i = s.nextChoice i := by
  simp [daStep, hi]
