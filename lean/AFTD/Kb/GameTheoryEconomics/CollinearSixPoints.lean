import AFTD.Prelude

/-!
# collinear_six_points

Topic: fair_division   Node: 716cb4289ffb

Provenance: helper lemma. step towards planar_necklace_three_agents_two_cuts

The six collinear points (0,0), (1,0), ..., (5,0) on the x-axis, as a finset of ℝ × ℝ.
-/

/-- The six points i ↦ (i, 0) for i < 6 on the x-axis. -/
noncomputable def collinear_six_points : Finset (ℝ × ℝ) := (Finset.range 6).image (fun i : ℕ => (((i : ℕ) : ℝ), (0 : ℝ)))
