import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences

/-!
# GS.propTarget

Topic: matching_markets   Node: 7498be4f2960

Provenance: formalization of a published result. Source: EconCSLib, `GS.propTarget`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The woman man `i` proposes to at cursor index `k` (none if out of bounds).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- The woman man `i` proposes to at cursor index `k` (none if out of bounds). -/
def GS.propTarget {n : ℕ} (m : Preferences n) (i : Fin n) (k : ℕ) : Option (Fin n) :=
  (m.prefs i)[k]?
