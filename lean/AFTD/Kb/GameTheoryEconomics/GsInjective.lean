import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.FinalAllWomenHold
import AFTD.Kb.GameTheoryEconomics.FinalHoldingInjective

/-!
# gs_injective

Topic: matching_markets   Node: a76ccb63f480

Provenance: formalization of a published result. Source: EconCSLib, `gs_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`gs w m` is injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `gs w m` is injective. -/
lemma gs_injective : Function.Injective (gs w m) := by
  intro j1 j2 heq
  simp only [gs] at heq
  obtain ⟨i1, hi1⟩ := final_all_women_hold w m j1
  obtain ⟨i2, hi2⟩ := final_all_women_hold w m j2
  simp [hi1, hi2] at heq; subst heq
  exact final_holding_injective w m j1 j2 i1 hi1 hi2
