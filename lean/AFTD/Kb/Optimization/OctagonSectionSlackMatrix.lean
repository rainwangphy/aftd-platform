import AFTD.Prelude

/-!
# octagon_section_slack_matrix

Topic: integer_programming   Node: 1ec807e05153

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The 8 × 8 rational slack matrix of the octagon P_2 = conv{(±2/3,0),(0,±2/3),(±1/2,±1/2)} which is the z=0 section of the biplanar octahedron Q_2 (arXiv:2610.04498 Theorem 7.1 at h=2): S_ij = 1 - (a_i x_j + b_i y_j), with facet normals a=(1/2,1/2,-1/2,-1/2,3/2,3/2,-3/2,-3/2), b=(3/2,-3/2,3/2,-3/2,1/2,-1/2,1/2,-1/2) and vertices (x,y)=(2/3,0),(1/2,1/2),(0,2/3),(-1/2,1/2),(-2/3,0),(-1/2,-1/2),(0,-2/3),(1/2,-1/2).
-/

/-- The concrete 8x8 rational slack matrix of the square-symmetric octagon P_2 (paper's Theorem 7.1 at h=2); the witness for the parent existential. -/
noncomputable def octagon_section_slack_matrix : Matrix (Fin 8) (Fin 8) ℝ := ![
  ![2/3, 0, 0, 1/2, 4/3, 2, 2, 3/2],
  ![2/3, 3/2, 2, 2, 4/3, 1/2, 0, 0],
  ![4/3, 1/2, 0, 0, 2/3, 3/2, 2, 2],
  ![4/3, 2, 2, 3/2, 2/3, 0, 0, 1/2],
  ![0, 0, 2/3, 3/2, 2, 2, 4/3, 1/2],
  ![0, 1/2, 4/3, 2, 2, 3/2, 2/3, 0],
  ![2, 3/2, 2/3, 0, 0, 1/2, 4/3, 2],
  ![2, 2, 4/3, 1/2, 0, 0, 2/3, 3/2]
]
