import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldingInjectiveStep

/-!
# holding_injective_run

Topic: matching_markets   Node: 0070dea9d404

Provenance: formalization of a published result. Source: EconCSLib, `holding_injective_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Over `daRun`, holding remains injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- Over `daRun`, holding remains injective. -/
lemma holding_injective_run (fuel : ℕ) (s : DAState n)
    (hinj : ∀ j1 j2 : Fin n, ∀ i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2) :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (daRun w m fuel s).holding j1 = some i → (daRun w m fuel s).holding j2 = some i → j1 = j2 := by
  induction fuel generalizing s with
  | zero   => exact hinj
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne
      · exact ih (daStep w m s) (holding_injective_step w m s hinj)
      · exact hinj
