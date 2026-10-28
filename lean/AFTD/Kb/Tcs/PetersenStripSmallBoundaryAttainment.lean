import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripWitness
import AFTD.Kb.Tcs.PetersenStripBoundary
import AFTD.Kb.Tcs.PetersenStripWitnessCard
import AFTD.Kb.Tcs.PetersenStripWitnessBoundaryCard
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# petersen_strip_small_boundary_attainment

Topic: graphs   Node: caa6cde6b4a1

Provenance: helper lemma. step towards petersen_strip_small_boundary_quadratic_extremum

For each natural number k ≥ 8, there exists a finite vertex set S in the generalized Petersen strip such that its boundary card is at most 2k + 1 and S.card = k^2/2 + 1.
-/

/-- For each natural number k ≥ 8, there exists a finite vertex set S in the generalized Petersen strip with boundary card at most 2k + 1 and S.card = k^2/2 + 1. -/
theorem petersen_strip_small_boundary_attainment (k : ℕ) (hk : 8 ≤ k) : ∃ S : Finset PetersenStripVertex, (petersen_strip_boundary k S).card ≤ 2 * k + 1 ∧ S.card = k ^ 2 / 2 + 1 := ⟨petersen_strip_witness k, petersen_strip_witness_boundary_card k hk, petersen_strip_witness_card k hk⟩
