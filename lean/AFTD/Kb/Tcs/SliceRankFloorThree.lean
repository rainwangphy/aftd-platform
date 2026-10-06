import AFTD.Prelude
import AFTD.Kb.Tcs.SliceRankFloor

/-!
# slice_rank_floor_three

Topic: quantum   Node: 0981b79180de

Provenance: formalization of a published result. Source: arXiv:2610.01024, Proposition 59

The slice-rank floor G(3) for the GF(8) multiplication oracle equals 20.
-/

/-- The slice-rank floor G(3) for the GF(8) oracle equals 20. -/
theorem slice_rank_floor_three : slice_rank_floor 3 = 20 := by
  rfl
