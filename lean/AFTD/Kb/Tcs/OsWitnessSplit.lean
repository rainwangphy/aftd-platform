import AFTD.Prelude

/-!
# os_witness_split

Topic: combinatorics   Node: 25b2a7071d94

Provenance: helper lemma. step towards oriented_star_ge_two_edges_not_os

The product digraphon 1_A(x) * 1_B(y) for A = (0, 1/2) and B = (1/2, 1): the indicator of the off-diagonal square [0,1]^2 restricted to a two-block split.
-/

/-- The mixed-case witness digraphon 1_A x 1_B with A = (0,1/2) and B = (1/2,1); its supports are disjoint, so the star density vanishes when both degrees are positive. -/
noncomputable def os_witness_split : ℝ → ℝ → ℝ := fun x y => Set.indicator (Set.Ioo (0:ℝ) (1/2)) (fun _ => (1:ℝ)) x * Set.indicator (Set.Ioo (1/2) 1) (fun _ => (1:ℝ)) y
