import AFTD.Prelude
import AFTD.Kb.Tcs.StarOccupancy

/-!
# star_occupancy_two_at_one

Topic: graphs   Node: ac17df9d1d12

Provenance: helper lemma. arXiv:2208.10475v2; OP-542

At activity lam = 1, the star graph K_{1,2} (the path P_3) has dominating occupancy equal to 2/3.
-/

/-- The star graph K_{1,2} at activity 1 has occupancy 2/3. -/
theorem star_occupancy_two_at_one : star_occupancy 2 1 = 2 / 3 := by
  unfold star_occupancy
  norm_num
