import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.HoldingRankMonoRun

/-!
# held_preserved_run

Topic: matching_markets   Node: f0974f343a70

Provenance: formalization of a published result. Source: EconCSLib, `held_preserved_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Once held, always held over `daRun`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- Once held, always held over `daRun`. -/
lemma held_preserved_run (fuel : ℕ) (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h', (daRun w m fuel s).holding j = some h' :=
  (holding_rank_mono_run w m fuel s j hh).imp fun _ ⟨eq, _⟩ => eq
