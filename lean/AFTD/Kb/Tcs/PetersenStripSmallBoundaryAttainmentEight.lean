import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripBoundary
import AFTD.Kb.Tcs.PetersenStripWitness
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# petersen_strip_small_boundary_attainment_eight

Topic: graphs   Node: edbbc8fa9f20

Provenance: formalization of a published result. Source: knowledge base OP-540; arXiv:2610.24059

In the generalized Petersen strip with step 8, there exists a finite vertex set S : Finset PetersenStripVertex such that (petersen_strip_boundary 8 S).card ≤ 17 and S.card = 33.
-/

/-- Attainment of the quadratic boundary extremum for k = 8. -/
theorem petersen_strip_small_boundary_attainment_eight : ∃ S : Finset PetersenStripVertex, (petersen_strip_boundary 8 S).card ≤ 17 ∧ S.card = 33 := ⟨petersen_strip_witness 8, by decide⟩
