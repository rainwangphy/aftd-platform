import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsESS
import AFTD.Kb.GameTheoryEconomics.IsNSS

/-!
# IsESS.isNSS

Topic: equilibria   Node: cfb3b1b0dcc7

Provenance: formalization of a published result. Source: EconCSLib, `IsESS.isNSS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every ESS is neutrally stable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {S : Type*} {u : S → S → ℝ} in
/-- Every ESS is neutrally stable. -/
theorem IsESS.isNSS {s : S} (h : IsESS u s) : IsNSS u s := by
  exact ⟨h.1, fun t heq => by
    by_cases hs : s = t
    · subst hs; exact le_refl _
    · exact le_of_lt (h.2 t heq hs)⟩
