import AFTD.Prelude

/-!
# collinear_six_coloring

Topic: fair_division   Node: acce219e1747

Provenance: helper lemma. step towards planar_necklace_three_agents_two_cuts

The coloring of the plane that is red (color 0) strictly left of the vertical line x = 3 and blue (color 1) elsewhere; on the six collinear points it gives R,R,R,B,B,B.
-/

/-- Two-coloring red/blue that realizes the pattern R,R,R,B,B,B on collinear_six_points. -/
noncomputable def collinear_six_coloring : (ℝ × ℝ) → Fin 2 := fun p => if p.1 < 3 then 0 else 1
