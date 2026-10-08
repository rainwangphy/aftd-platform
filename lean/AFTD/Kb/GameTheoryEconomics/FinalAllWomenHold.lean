import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.FinalAllMenHeld
import AFTD.Kb.GameTheoryEconomics.FinalHoldingInjective

/-!
# final_all_women_hold

Topic: matching_markets   Node: 89afcb77b3f9

Provenance: formalization of a published result. Source: EconCSLib, `final_all_women_hold`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At termination, every woman holds some man.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- At termination, every woman holds some man. -/
lemma final_all_women_hold :
    ∀ j : Fin n, ∃ i : Fin n, (finalState w m).holding j = some i := by
  intro j
  by_contra hnone
  push_neg at hnone
  -- j holds nobody, but every man is held by some woman ≠ j (pigeon-hole).
  have hall := final_all_men_held w m
  have hinj := final_holding_injective w m
  have hf : ∀ i : Fin n, ∃ j' : Fin n, j' ≠ j ∧ (finalState w m).holding j' = some i := by
    intro i
    obtain ⟨j', hj'⟩ := hall i
    exact ⟨j', fun heq => absurd (heq ▸ hj') (hnone i), hj'⟩
  -- Inject Fin n → (univ \ {j}) of size n-1 → contradiction.
  let f : Fin n → (Finset.univ.erase j : Finset (Fin n)) := fun i =>
    ⟨(hf i).choose, Finset.mem_erase.mpr ⟨(hf i).choose_spec.1, Finset.mem_univ _⟩⟩
  have hfinj : Function.Injective f := by
    intro i1 i2 heq
    have h1 : (finalState w m).holding ((hf i1).choose) = some i1 := (hf i1).choose_spec.2
    have h2 : (finalState w m).holding ((hf i2).choose) = some i2 := (hf i2).choose_spec.2
    have hv : (hf i1).choose = (hf i2).choose := congrArg Subtype.val heq
    rw [hv] at h1
    exact Option.some.inj (h1.symm.trans h2)
  have hcard : (Finset.univ.erase j : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have : Fintype.card (Fin n) ≤ Fintype.card ↥(Finset.univ.erase j : Finset (Fin n)) :=
    Fintype.card_le_of_injective _ hfinj
  rw [Fintype.card_coe, hcard, Fintype.card_fin] at this
  exact absurd this (by have hpos := NeZero.pos n; omega)
