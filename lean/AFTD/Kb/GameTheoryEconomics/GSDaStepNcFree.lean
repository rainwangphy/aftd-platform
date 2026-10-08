import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# GS.daStep_nc_free

Topic: matching_markets   Node: 659389bbacec

Provenance: formalization of a published result. Source: EconCSLib, `GS.daStep_nc_free`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.daStep_nc_free
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
lemma GS.daStep_nc_free {n : ℕ} {w m : Preferences n} {s : DAState n} {i : Fin n}
    (hi : isFree s i = true) : (daStep w m s).nextChoice i = s.nextChoice i + 1 := by
  simp [daStep, hi]
