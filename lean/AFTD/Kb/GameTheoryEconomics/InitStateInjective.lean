import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.GSPreferences

/-!
# initState_injective

Topic: matching_markets   Node: 7f9441d6d5bb

Provenance: formalization of a published result. Source: EconCSLib, `initState_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`initState` has trivially injective holding (all `none`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `initState` has trivially injective holding (all `none`). -/
lemma initState_injective :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (initState n).holding j1 = some i → (initState n).holding j2 = some i → j1 = j2 := by
  intro j1 j2 i h1; simp [initState] at h1
