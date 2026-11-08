import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193HomCycleStep

/-!
# op_193_chromaticNumber_le_cycle_step

Topic: graphs   Node: ca707ea4cfc7

Provenance: formalization of a published result. Source: arXiv:2610.17884 Lemma 2.12 -- The chromatic number of G-stable Kneser graphs

For all integers k ≥ 2 and r ≥ 2 * k - 2, the chromatic number of the G-stable Kneser graph KG(C_{r+2} ⊔ K_1, k) is at most the chromatic number of the G-stable Kneser graph KG(C_r ⊔ K_1, k-1).
-/

/-- Monotonicity step: the chromatic number of KG(C_{r+2} ⊔ K_1, k) is at most that of KG(C_r ⊔ K_1, k-1). -/
theorem op_193_chromaticNumber_le_cycle_step (k r : ℕ) (hk : 2 ≤ k) (hr : 2 * k - 2 ≤ r) :
    (GStableKneser ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber ≤
      (GStableKneser ((SimpleGraph.cycleGraph r).sum (⊥ : SimpleGraph Unit)) (k - 1)).chromaticNumber :=
  Nonempty.elim (op_193_hom_cycle_step k r hk hr) SimpleGraph.chromaticNumber_mono_of_hom
