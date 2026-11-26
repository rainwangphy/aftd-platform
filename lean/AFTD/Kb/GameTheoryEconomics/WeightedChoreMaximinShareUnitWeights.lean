import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WeightedChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# weighted_chore_maximin_share_unit_weights

Topic: fair_division   Node: 00240eb7e422

Provenance: helper lemma. Normalization sanity check for OP-2461.

Unit weights recover the existing unweighted chore maximin share.
-/

theorem weighted_chore_maximin_share_unit_weights {m n : ℕ} (u : Fin m → ℝ) (i : Fin n) : weighted_chore_maximin_share (fun _ : Fin n => 1) u i = chore_maximin_share n u := by
  simp [weighted_chore_maximin_share, chore_maximin_share]
