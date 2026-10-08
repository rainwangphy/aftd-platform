import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# GS.propTarget_lt

Topic: matching_markets   Node: 06a7fb367df9

Provenance: formalization of a published result. Source: EconCSLib, `GS.propTarget_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`propTarget` returns `some` when `k < n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- `propTarget` returns `some` when `k < n`. -/
lemma GS.propTarget_lt {n : ℕ} (m : Preferences n) (i : Fin n) {k : ℕ} (hk : k < n) :
    ∃ j, propTarget m i k = some j := by
  have hlen : k < (m.prefs i).length := by rwa [(m.valid i).2]
  exact ⟨(m.prefs i)[k], List.getElem?_eq_getElem hlen⟩
