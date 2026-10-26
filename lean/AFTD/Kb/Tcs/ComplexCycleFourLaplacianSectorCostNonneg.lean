import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplacianSectorCost

/-!
# complex_cycle_four_laplacian_sector_cost_nonneg

Topic: graphs   Node: f13b2a35e06f

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

The sum of the Laplacian sector costs around any closed four-step complex cycle is nonnegative, including repeated vertices.
-/

theorem complex_cycle_four_laplacian_sector_cost_nonneg (a b c d : ℂ) :
    0 ≤ complex_laplacian_sector_cost a b + complex_laplacian_sector_cost b c + complex_laplacian_sector_cost c d + complex_laplacian_sector_cost d a := by
  dsimp [complex_laplacian_sector_cost]
  nlinarith only [
    sq_nonneg (a.re - c.re - (b.im - d.im)),
    sq_nonneg (a.im - c.im + (b.re - d.re)),
    sq_nonneg (a.re - b.re + c.re - d.re),
    sq_nonneg (a.im - b.im + c.im - d.im)]
