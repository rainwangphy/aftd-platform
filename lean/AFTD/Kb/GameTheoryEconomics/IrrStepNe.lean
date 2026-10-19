import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IrrStep
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# irr_step_ne

Topic: fair_division   Node: 03b2e4099ff3

Provenance: helper lemma. Sanity lemma for irr_step.

An iterated best-response step always changes the bid profile, since the moving agent strictly improves.
-/

theorem irr_step_ne {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (v : N → G → ℝ) (seq : List N) (adm : (N → Fin m ≃ G) → N → (Fin m ≃ G) → Prop)
    (b b' : N → Fin m ≃ G) (h : irr_step v seq adm b b') : b' ≠ b := by
  rintro rfl
  rcases h with ⟨i, ⟨r, hr_adm, hr_lt⟩, ⟨r_br, hr_br_adm, hr_br_eq, h_max⟩⟩
  have h_le := h_max r hr_adm
  linarith
