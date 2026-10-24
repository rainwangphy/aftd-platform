import AFTD.Prelude

/-!
# octahedron_vertex_vectors

Topic: integer_programming   Node: 352af938b047

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The six octahedron vertex vectors c_k ∈ ℝ^4 of Q_2 (paper's Remark 7.2), k = u+,u-,v+,v-,w+,w-: c_{u±}=((1+√3)/4,(1-√3)/4,∓1/2,0), c_{v±}=((1+√3)/4,-(1-√3)/4,0,∓1/2), c_{w±}=(√2/2,∓√2/2,0,0).
-/

/-- Vertex factor vectors of the octahedron lift (order u+,u-,v+,v-,w+,w-). -/
noncomputable def octahedron_vertex_vectors : Fin 6 → Fin 4 → ℝ := ![![(1+Real.sqrt 3)/4, (1-Real.sqrt 3)/4, -1/2, 0],
     ![ (1+Real.sqrt 3)/4, (1-Real.sqrt 3)/4, 1/2, 0],
     ![ (1+Real.sqrt 3)/4, -(1-Real.sqrt 3)/4, 0, -1/2],
     ![ (1+Real.sqrt 3)/4, -(1-Real.sqrt 3)/4, 0, 1/2],
     ![ Real.sqrt 2/2, -Real.sqrt 2/2, 0, 0],
     ![ Real.sqrt 2/2, Real.sqrt 2/2, 0, 0]]
