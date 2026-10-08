import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSNotIsFreeIff
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem

/-!
# not_free_of_nc_ge

Topic: matching_markets   Node: 54141e852469

Provenance: formalization of a published result. Source: EconCSLib, `not_free_of_nc_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`nextChoice i ≥ n` + injectivity + `JInv` → man `i` is not free.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `nextChoice i ≥ n` + injectivity + `JInv` → man `i` is not free. -/
lemma not_free_of_nc_ge (m : Preferences n) (s : DAState n) (i : Fin n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (hnc : n ≤ s.nextChoice i) :
    isFree s i = false := by
  rw [not_isFree_iff]
  have hall : ∀ j : Fin n, ∃ h, s.holding j = some h := by
    intro j
    apply hj i j
    have hmem : j ∈ m.prefs i := pref_list_mem _ (m.valid i).1 (m.valid i).2 j
    rw [List.take_of_length_le (by rw [(m.valid i).2]; exact hnc)]
    exact hmem
  -- The function j ↦ (hall j).choose is injective (by holding injectivity),
  -- hence surjective on the finite type Fin n.
  let f : Fin n → Fin n := fun j => (hall j).choose
  have hfinj : Function.Injective f := by
    intro j1 j2 heq
    exact hinj j1 j2 (hall j1).choose (hall j1).choose_spec
      (show s.holding j2 = some (f j1) from heq ▸ (hall j2).choose_spec)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  obtain ⟨j, rfl⟩ := hfsurj i
  exact ⟨j, (hall j).choose_spec⟩
