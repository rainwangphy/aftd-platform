import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# holding_rank_mono_step

Topic: matching_markets   Node: c8a0f0a88e48

Provenance: formalization of a published result. Source: EconCSLib, `holding_rank_mono_step`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

After one `daStep`, woman `j`'s held man's rank can only decrease (she only upgrades).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- After one `daStep`, woman `j`'s held man's rank can only decrease (she only upgrades). -/
lemma holding_rank_mono_step (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h' : Fin n, (daStep w m s).holding j = some h' ∧
      (w.prefs j).idxOf h' ≤ (w.prefs j).idxOf hval := by
  simp only [daStep]
  set pl := (Finset.univ.filter (fun i =>
    isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList
  cases pl.argmin (fun i => (w.prefs j).idxOf i) with
  | none => exact ⟨hval, by simp [hh], le_refl _⟩
  | some p =>
      simp only [hh]
      split_ifs with hlt
      · exact ⟨p, rfl, Nat.le_of_lt hlt⟩
      · exact ⟨hval, rfl, le_refl _⟩
