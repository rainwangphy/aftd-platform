import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSInitState

/-!
# GS.finalState

Topic: matching_markets   Node: b010102bdb44

Provenance: formalization of a published result. Source: EconCSLib, `GS.finalState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`finalState`: run `daRun` with fuel `n*n + 1` from `initState`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- `finalState`: run `daRun` with fuel `n*n + 1` from `initState`. -/
noncomputable def GS.finalState {n : ℕ} (w m : Preferences n) : DAState n :=
  daRun w m (n * n + 1) (initState n)
