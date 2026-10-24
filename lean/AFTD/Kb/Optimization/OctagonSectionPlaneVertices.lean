import AFTD.Prelude

/-!
# octagon_section_plane_vertices

Topic: integer_programming   Node: 3afe71508ddc

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The eight vertices of the octagon P_2 in cyclic order: v_j = (2/3,0),(1/2,1/2),(0,2/3),(-1/2,1/2),(-2/3,0),(-1/2,-1/2),(0,-2/3),(1/2,-1/2).
-/

/-- The eight octagon vertices as points of the plane Fin 2 -> R. -/
noncomputable def octagon_section_plane_vertices : Fin 8 → Fin 2 → ℝ := ![![2/3,0],![1/2,1/2],![0,2/3],![-1/2,1/2],![-2/3,0],![-1/2,-1/2],![0,-2/3],![1/2,-1/2]]
