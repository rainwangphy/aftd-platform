import AFTD.Prelude

/-!
# os_witness_rect_g

Topic: combinatorics   Node: c39da3bcee4a

Provenance: helper lemma. step towards oriented_star_ge_two_edges_not_os

The indicator function of the interval (0, 1/4) inside [0, 1].
-/

/-- The indicator g = 1_{(0,1/4)} of the interval of length 1/4 in a corner of [0,1], used as the profile of the row/column of the pure-case witness. -/
noncomputable def os_witness_rect_g : ℝ → ℝ := fun y => Set.indicator (Set.Ioo (0:ℝ) (1/4)) (fun _ => (1:ℝ)) y
