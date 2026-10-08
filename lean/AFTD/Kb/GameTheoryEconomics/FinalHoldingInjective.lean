import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.HoldingInjectiveRun
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.InitStateInjective

/-!
# final_holding_injective

Topic: matching_markets   Node: 4e14efd83ddc

Provenance: formalization of a published result. Source: EconCSLib, `final_holding_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`finalState` holding is injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `finalState` holding is injective. -/
lemma final_holding_injective :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (finalState w m).holding j1 = some i → (finalState w m).holding j2 = some i → j1 = j2 :=
  holding_injective_run w m (n * n + 1) (initState n) (initState_injective (n := n))
