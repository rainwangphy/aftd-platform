import AFTD.Prelude

/-!
# octagon_h2_slack_matrix

Topic: integer_programming   Node: 78d443bb07ee

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The explicit 8 × 8 rational matrix from arXiv:2610.04498 Theorem 7.1 with parameter h = 2.
-/

/-- The explicit 8 × 8 slack matrix for the planar octagon obtained as the horizontal section z = 0 of the biplanar octahedron Q_h with parameter h = 2 (arXiv:2610.04498 Theorem 7.1). -/
noncomputable def octagon_h2_slack_matrix : Matrix (Fin 8) (Fin 8) ℝ := ![
  ![0, 0, 1/2, 4/3, 2, 2, 3/2, 2/3],
  ![1/2, 0, 0, 2/3, 3/2, 2, 2, 4/3],
  ![3/2, 2/3, 0, 0, 1/2, 4/3, 2, 2],
  ![2, 4/3, 1/2, 0, 0, 2/3, 3/2, 2],
  ![2, 2, 3/2, 2/3, 0, 0, 1/2, 4/3],
  ![3/2, 2, 2, 4/3, 1/2, 0, 0, 2/3],
  ![1/2, 4/3, 2, 2, 3/2, 2/3, 0, 0],
  ![0, 2/3, 3/2, 2, 2, 4/3, 1/2, 0]
]
