import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep

/-!
# GS.daRun

Topic: matching_markets   Node: 0f7f8688c0f6

Provenance: formalization of a published result. Source: EconCSLib, `GS.daRun`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Run DA for at most `fuel` steps, stopping early if no free men remain.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- Run DA for at most `fuel` steps, stopping early if no free men remain. -/
noncomputable def GS.daRun {n : ℕ} (w m : Preferences n) : ℕ → DAState n → DAState n
  | 0,        s => s
  | fuel + 1, s => if (freeMenSet s).Nonempty then daRun w m fuel (daStep w m s) else s
