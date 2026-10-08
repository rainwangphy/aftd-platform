import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSNotIsFreeIff
import AFTD.Kb.GameTheoryEconomics.FinalStateNoFreeMen

/-!
# final_all_men_held

Topic: matching_markets   Node: 9651f514a11b

Provenance: formalization of a published result. Source: EconCSLib, `final_all_men_held`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At termination, every man is held by some woman.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- At termination, every man is held by some woman. -/
lemma final_all_men_held :
    ∀ i : Fin n, ∃ j : Fin n, (finalState w m).holding j = some i := by
  intro i; exact (not_isFree_iff _ _).mp (finalState_no_free_men w m i)
