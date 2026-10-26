import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplacianSectorCost

/-!
# complex_laplacian_sector_cost_self

Topic: graphs   Node: 291f7a2d7d08

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

The Laplacian sector cost of a loop is zero.
-/

theorem complex_laplacian_sector_cost_self (u : ℂ) : complex_laplacian_sector_cost u u = 0 := by simp [complex_laplacian_sector_cost]
