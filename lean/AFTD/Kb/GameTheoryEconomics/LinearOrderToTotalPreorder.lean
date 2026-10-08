import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# LinearOrder.toTotalPreorder

Topic: social_choice   Node: a5664b1fed32

Provenance: formalization of a published result. Source: EconCSLib, `LinearOrder.toTotalPreorder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every `LinearOrder` is a `TotalPreorder`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Every `LinearOrder` is a `TotalPreorder`. -/
instance (priority := 100) LinearOrder.toTotalPreorder [LinearOrder A] : TotalPreorder A where
  le_total := LinearOrder.le_total
