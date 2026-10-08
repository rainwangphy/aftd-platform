import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.GSDaStep

/-!
# proposal_rank_bound

Topic: matching_markets   Node: 034ef32c150d

Provenance: formalization of a published result. Source: EconCSLib, `proposal_rank_bound`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

When free man `j` proposes to woman `i` in `daStep`, the resulting hold has rank ≤ j.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- When free man `j` proposes to woman `i` in `daStep`, the resulting hold has rank ≤ j. -/
lemma proposal_rank_bound (w m : Preferences n) (s : DAState n) (j i : Fin n)
    (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i) :
    ∃ h : Fin n, (daStep w m s).holding i = some h ∧
      (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j := by
  -- j is in proposerList i
  have hj_in : j ∈ (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some i))).val.toList :=
    Multiset.mem_toList.mpr (Finset.mem_val.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hfj, hpt]⟩))
  set pl := (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some i))).val.toList with hpl_def
  have hne_pl : pl ≠ [] := List.ne_nil_of_mem hj_in
  -- argmin returns some q with rank ≤ j's rank
  have hbn : ∃ q : Fin n, pl.argmin (fun k => (w.prefs i).idxOf k) = some q :=
    (Option.ne_none_iff_exists.mp (List.argmin_eq_none.not.mpr hne_pl)).imp
      (fun _ h => h.symm)
  obtain ⟨q, hq⟩ := hbn
  have hq_le : (w.prefs i).idxOf q ≤ (w.prefs i).idxOf j :=
    List.le_of_mem_argmin hj_in (show q ∈ pl.argmin (fun k => (w.prefs i).idxOf k) from hq)
  -- daStep holding i = some h with rank ≤ q ≤ j
  simp only [daStep, ← hpl_def]
  cases hs : s.holding i with
  | none =>
      simp only [hs, hq]
      exact ⟨q, rfl, hq_le⟩
  | some h =>
      simp only [hs, hq]
      split_ifs with hlt
      · exact ⟨q, rfl, hq_le⟩
      · exact ⟨h, rfl, Nat.le_trans (Nat.le_of_not_lt hlt) hq_le⟩
