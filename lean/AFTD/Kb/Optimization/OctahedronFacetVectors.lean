import AFTD.Prelude

/-!
# octahedron_facet_vectors

Topic: integer_programming   Node: f5669e126625

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The eight facet vectors q_i ∈ ℝ^4 of the octahedron Q_2 (paper's Remark 7.2, index i = (s,t,ε) in the same order as the octagon normal (a_i,b_i)): q_0=(1,1,1,√3), q_1=(1,1,1,-√3), q_2=(1,1,-1,√3), q_3=(1,1,-1,-√3), q_4=(1,-1,√3,1), q_5=(1,-1,√3,-1), q_6=(1,-1,-√3,1), q_7=(1,-1,-√3,-1).
-/

/-- Facet factor vectors of the octahedron lift, indexed to match the octagon facet ordering. -/
noncomputable def octahedron_facet_vectors : Fin 8 → Fin 4 → ℝ := ![![1,1,1, Real.sqrt 3], ![1,1,1, -Real.sqrt 3], ![1,1,-1, Real.sqrt 3], ![1,1,-1, -Real.sqrt 3],
     ![1,-1, Real.sqrt 3, 1], ![1,-1, Real.sqrt 3, -1], ![1,-1, -Real.sqrt 3, 1], ![1,-1, -Real.sqrt 3, -1]]
