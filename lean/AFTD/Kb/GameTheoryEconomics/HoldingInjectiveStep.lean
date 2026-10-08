import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.PlFreeProps
import AFTD.Kb.GameTheoryEconomics.GSIsFreeIff

/-!
# holding_injective_step

Topic: matching_markets   Node: ed3ec84dc6a0

Provenance: formalization of a published result. Source: EconCSLib, `holding_injective_step`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In `daStep`, `holding` remains injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- In `daStep`, `holding` remains injective. -/
lemma holding_injective_step (s : DAState n)
    (hinj : ∀ j1 j2 : Fin n, ∀ i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2) :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (daStep w m s).holding j1 = some i → (daStep w m s).holding j2 = some i → j1 = j2 := by
  intro j1 j2 i hj1 hj2
  -- The proposerList and bestNew for each woman
  let pl : Fin n → List (Fin n) := fun j =>
    (Finset.univ.filter (fun k =>
      isFree s k && (propTarget m k (s.nextChoice k) == some j))).val.toList
  have pl_disj : ∀ k : Fin n, ∀ j1' j2' : Fin n,
      k ∈ pl j1' → k ∈ pl j2' → j1' = j2' := by
    intro k j1' j2' hk1 hk2
    exact Option.some.inj
      ((pl_free_props s m j1' k hk1).2.symm.trans (pl_free_props s m j2' k hk2).2)
  let bn : Fin n → Option (Fin n) := fun j =>
    (pl j).argmin (fun k => (w.prefs j).idxOf k)
  have bn_mem : ∀ j p : Fin n, bn j = some p → p ∈ pl j := fun j p hp =>
    List.argmin_mem hp
  -- `newHolding j = some i` means i came via bn j or from s.holding j
  have result_source : ∀ j : Fin n,
      (daStep w m s).holding j = some i →
      bn j = some i ∨ s.holding j = some i := by
    intro j hj
    simp only [daStep] at hj
    rcases hs : s.holding j with _ | h <;> rcases hb : bn j with _ | p <;>
    simp only [hs, show (Finset.univ.filter (fun k =>
        isFree s k && (propTarget m k (s.nextChoice k) == some j))).val.toList.argmin
        (fun k => idxOf k (w.prefs j)) = bn j from rfl] at hj <;>
    simp_all [bn] <;> split_ifs at hj with hlt <;> simp_all
  rcases result_source j1 hj1 with hbn1 | hold1
  · -- i came via proposals to j1 → i was free in s
    have hi_free : isFree s i = true := (pl_free_props s m j1 i (bn_mem j1 i hbn1)).1
    rcases result_source j2 hj2 with hbn2 | hold2
    · -- both via proposals → j1 = j2 (same man can only propose to one woman)
      exact pl_disj i j1 j2 (bn_mem j1 i hbn1) (bn_mem j2 i hbn2)
    · -- j2 via old holding: i was free but s.holding j2 = some i → contradiction
      rw [isFree_iff] at hi_free; exact absurd hold2 (hi_free j2)
  · rcases result_source j2 hj2 with hbn2 | hold2
    · -- j1 via old holding, j2 via proposals → contradiction
      have hi_free : isFree s i = true := (pl_free_props s m j2 i (bn_mem j2 i hbn2)).1
      rw [isFree_iff] at hi_free; exact absurd hold1 (hi_free j1)
    · -- both via old holding → induction hypothesis
      exact hinj j1 j2 i hold1 hold2
