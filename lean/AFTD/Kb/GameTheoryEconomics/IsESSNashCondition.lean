import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsESS

/-!
# IsESS.nash_condition

Topic: equilibria   Node: 10e36175c9e0

Provenance: formalization of a published result. Source: EconCSLib, `IsESS.nash_condition`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ESS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ESS satisfies the symmetric Nash condition. [MSZ 5.51]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {S : Type*} {u : S → S → ℝ} in
/-- An ESS satisfies the symmetric Nash condition. [MSZ 5.51] -/
theorem IsESS.nash_condition {s : S} (h : IsESS u s) :
    ∀ t, u s s ≥ u t s := h.1
