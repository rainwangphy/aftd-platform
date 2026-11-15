import AFTD.Prelude
import AFTD.Kb.Physics.NoonRealignWitness

/-!
# op_1693_noon_witness_symm

Topic: quantum_mechanics   Node: b485f5358f32

Provenance: formalization of a published result. Source: arXiv:2611.17021

For every natural number N, balance parameter q in Real, and transmissivities x, y in Real, the realignment witness satisfies noon_realign_witness N (1 - q) y x = noon_realign_witness N q x y.
-/

/-- Symmetry of the NOON realignment witness under exchange of modes and balance parameter. -/
theorem op_1693_noon_witness_symm (N : ℕ) (q x y : ℝ) :
    noon_realign_witness N (1 - q) y x = noon_realign_witness N q x y := by
  unfold noon_realign_witness
  have h1 : 4 * (1 - q) * (1 - (1 - q)) * (y * x) ^ N = 4 * q * (1 - q) * (x * y) ^ N := by
    rw [mul_comm y x]
    ring
  rw [h1]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring
