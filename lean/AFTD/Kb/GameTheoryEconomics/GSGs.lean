import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState

/-!
# GS.gs

Topic: matching_markets   Node: 34914aed155a

Provenance: formalization of a published result. Source: EconCSLib, `GS.gs`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Gale-Shapley function: woman `j`'s partner at termination.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- The Gale-Shapley function: woman `j`'s partner at termination. -/
noncomputable def GS.gs {n : ℕ} [NeZero n] (w m : Preferences n) : Fin n → Fin n := fun j =>
  (finalState w m).holding j |>.getD default
