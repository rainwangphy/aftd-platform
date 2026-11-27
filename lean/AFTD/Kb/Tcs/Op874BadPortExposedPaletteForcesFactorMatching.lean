import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BadPortColorCoverForcesFactorMatching
import AFTD.Kb.Tcs.Op874MatchingPortHighIsFactorColor

/-!
# op874_bad_port_exposed_palette_forces_factor_matching

Topic: graphs   Node: b5e2d2194f66

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

Under the stated matching, ownership, four-high-color palette, and interface constraints, if every nonowner matching port exposes a high color outside the common pair, the owned factor edges form a perfect matching.
-/

theorem op874_bad_port_exposed_palette_forces_factor_matching {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate own : V → V) (step : V → Fin 2 → V)
    (col hidden : V → Fin 2 → Fin 6) (exposed : V → Fin 6)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (howner : ∀ v, own v = mate v ∨ ∃ i, own v = step v i)
    (hflag : ∀ v, flag v = true ↔ own v = mate v)
    (hsym : ∀ v i, ∃ j, step (step v i) j = v)
    (hdist : ∀ v, step v 0 ≠ step v 1)
    (hnomatch : ∀ v i, step v i ≠ mate v)
    (hselected : ∀ v i, 4 ≤ (col v i).val →
      own v = step v i ∨ own (step v i) = v)
    (hpalette : ∀ v, flag v = true →
      2 ≤ (col v 0).val ∧ 2 ≤ (col v 1).val ∧
      2 ≤ (hidden v 0).val ∧ 2 ≤ (hidden v 1).val ∧
      col v 0 ≠ col v 1 ∧ col v 0 ≠ hidden v 0 ∧
      col v 0 ≠ hidden v 1 ∧ col v 1 ≠ hidden v 0 ∧
      col v 1 ≠ hidden v 1 ∧ hidden v 0 ≠ hidden v 1)
    (hdisjoint : ∀ v, flag v = true →
      exposed (mate v) ≠ hidden v 0 ∧ exposed (mate v) ≠ hidden v 1)
    (hbad : ∀ v, flag v = true → 4 ≤ (exposed (mate v)).val) :
    ∀ v, ∃! i, own v = step v i ∨ own (step v i) = v := by
  apply op874_bad_port_color_cover_forces_factor_matching flag mate own step col hmate hflip howner hflag hsym hdist hnomatch hselected
  intro v hv
  obtain ⟨hc0,hc1,hh0,hh1,hnc,hc0h0,hc0h1,hc1h0,hc1h1,hnh⟩ := hpalette v hv
  obtain ⟨hd0,hd1⟩ := hdisjoint v hv
  have he := op874_matching_port_high_is_factor_color (col v 0) (col v 1)
    (hidden v 0) (hidden v 1) (exposed (mate v)) hc0 hc1 hh0 hh1 hnc hc0h0 hc0h1 hc1h0 hc1h1 hnh hd0 hd1 (by have := hbad v hv; omega)
  rcases he with he | he
  · refine ⟨0, ?_⟩
    rw [←he]
    exact hbad v hv
  · refine ⟨1, ?_⟩
    rw [←he]
    exact hbad v hv
