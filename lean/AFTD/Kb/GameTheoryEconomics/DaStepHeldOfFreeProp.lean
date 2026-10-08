import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.GSDaStep

/-!
# daStep_held_of_free_prop

Topic: matching_markets   Node: b86dc7c3d34e

Provenance: formalization of a published result. Source: EconCSLib, `daStep_held_of_free_prop`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Free man `i` proposing to woman `p` makes her held in `daStep`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- Free man `i` proposing to woman `p` makes her held in `daStep`. -/
lemma daStep_held_of_free_prop (w m : Preferences n) (s : DAState n) (i p : Fin n)
    (hfi : isFree s i = true) (hpt : propTarget m i (s.nextChoice i) = some p) :
    ∃ h : Fin n, (daStep w m s).holding p = some h := by
  have hi_in : i ∈ (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList :=
    Multiset.mem_toList.mpr (Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hfi, hpt]⟩))
  -- The proposer list is nonempty (i is in it), so argmin returns Some.
  set pl := (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList with hpl_def
  have hne_pl : pl ≠ [] := List.ne_nil_of_mem hi_in
  have hbn : ∃ q : Fin n, pl.argmin (fun k => (w.prefs p).idxOf k) = some q :=
    (Option.ne_none_iff_exists.mp (List.argmin_eq_none.not.mpr hne_pl)).imp (fun _ h => h.symm)
  obtain ⟨q, hq⟩ := hbn
  simp only [daStep, ← hpl_def]
  cases hs : s.holding p with
  | none   => simp only [hs, hq]; exact ⟨q, rfl⟩
  | some h => simp only [hs, hq]; split_ifs <;> exact ⟨_, rfl⟩
