import AFTD.Prelude

/-!
# octagon_vertex_weights

Topic: integer_programming   Node: 2023627c184b

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

For each octagon vertex v_j, the nonnegative barycentric weights μ_j on the octahedron vertices, expressing v_j as a point of an octahedron edge (z=0 section): μ_0=(2/3,0,0,0,0,1/3) [v_0 on edge u+w-], μ_1=(1/2,0,1/2,0,0,0) [edge u+v+], μ_2=(0,0,2/3,0,1/3,0) [edge v+w+], μ_3=(0,1/2,1/2,0,0,0), μ_4=(0,2/3,0,0,0,1/3), μ_5=(0,1/2,0,1/2,0,0), μ_6=(0,0,0,2/3,1/3,0), μ_7=(1/2,0,0,1/2,0,0).
-/

/-- Barycentric weights of each octagon vertex in the octahedron (all nonnegative, each row sums to 1). -/
noncomputable def octagon_vertex_weights : Fin 8 → Fin 6 → ℝ := ![![2/3,0,0,0,0,1/3], ![1/2,0,1/2,0,0,0], ![0,0,2/3,0,1/3,0], ![0,1/2,1/2,0,0,0],
     ![0,2/3,0,0,0,1/3], ![0,1/2,0,1/2,0,0], ![0,0,0,2/3,1/3,0], ![1/2,0,0,1/2,0,0]]
