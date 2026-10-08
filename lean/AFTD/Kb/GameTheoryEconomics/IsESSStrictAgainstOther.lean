import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsESS

/-!
# IsESS.strict_against_other

Topic: equilibria   Node: a8ec87556295

Provenance: formalization of a published result. Source: EconCSLib, `IsESS.strict_against_other`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Distinct ESS are strictly separated: if `s ≠ t` are both ESS, then `u(s,s) > u(t,s)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {S : Type*} {u : S → S → ℝ} in
/-- Distinct ESS are strictly separated: if `s ≠ t` are both ESS, then `u(s,s) > u(t,s)`. -/
theorem IsESS.strict_against_other {s t : S}
    (hs : IsESS u s) (ht : IsESS u t) (hne : s ≠ t) :
    u s s > u t s := by
  have hge := hs.1 t
  by_contra h
  push_neg at h
  have heq : u s s = u t s := le_antisymm h hge
  have hstab := hs.2 t heq hne
  linarith [ht.1 s]
