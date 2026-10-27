import AFTD.Prelude
import AFTD.Kb.Tcs.StarOccupancy

/-!
# star_occupancy_one_at_one

Topic: graphs   Node: 4e6cdecd7fb1

Provenance: helper lemma. arXiv:2208.10475v2; OP-542

At activity lam = 1, the star graph K_{1,1} (the single edge K_2) has dominating occupancy equal to 2/3.
-/

/-- The star graph K_{1,1} at activity 1 has occupancy 2/3. -/
theorem star_occupancy_one_at_one : star_occupancy 1 1 = 2 / 3 := by
  unfold star_occupancy
  norm_num
