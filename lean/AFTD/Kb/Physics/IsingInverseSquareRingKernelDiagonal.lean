import AFTD.Prelude
import AFTD.Kb.Physics.IsingInverseSquareRingKernel

/-!
# ising_inverse_square_ring_kernel_diagonal

Topic: statistical_mechanics   Node: ff7dc4b0f474

Provenance: helper lemma. arXiv:2610.39815, Sections 2–4; helper for OP-806.

The periodized ring kernel has zero diagonal.
-/

theorem ising_inverse_square_ring_kernel_diagonal (L : ℕ) (i : Fin L) : ising_inverse_square_ring_kernel L i i = 0 := by
  simp [ising_inverse_square_ring_kernel]
