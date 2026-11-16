import AFTD.Prelude

/-!
# graphon_edge_density

Topic: graphs   Node: 74e1d06841e4

Provenance: formalization of a published result. Source: arXiv:2611.17885 Section 1

The edge density t(K_2, W) of a graphon W is the integral of W(x, y) over the unit square [0, 1] × [0, 1].
-/

/-- The edge density t(K_2, W) of a graphon W. -/
noncomputable def graphon_edge_density (W : ℝ → ℝ → ℝ) : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) 1, W x y
