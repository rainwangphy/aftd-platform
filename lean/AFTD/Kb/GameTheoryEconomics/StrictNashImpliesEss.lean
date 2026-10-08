import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsESS

/-!
# strict_nash_implies_ess

Topic: equilibria   Node: c13869f650a5

Provenance: formalization of a published result. Source: EconCSLib, `strict_nash_implies_ess`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strict symmetric Nash equilibrium is automatically ESS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {S : Type*} {u : S → S → ℝ} in
/-- A strict symmetric Nash equilibrium is automatically ESS. -/
theorem strict_nash_implies_ess {s : S}
    (hstrict : ∀ t, t ≠ s → u s s > u t s) : IsESS u s := by
  refine ⟨fun t => ?_, fun t heq hne => ?_⟩
  · by_cases h : t = s
    · subst h; exact le_refl _
    · exact le_of_lt (hstrict t h)
  · exact absurd heq (ne_of_gt (hstrict t hne.symm))
