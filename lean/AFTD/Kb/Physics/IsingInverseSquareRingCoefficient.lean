import AFTD.Prelude
import AFTD.Kb.Physics.IsingInverseSquareRingFreeEnergy

/-!
# ising_inverse_square_ring_coefficient

Topic: statistical_mechanics   Node: 0ed79194d630

Provenance: helper lemma. arXiv:2610.39815, Sections 2–4; helper for OP-806.

The order-n finite-ring coupling coefficient at field h is the nth derivative at x=0 of the reduced free energy, divided by n factorial.
-/

noncomputable def ising_inverse_square_ring_coefficient (n L : ℕ) (h : ℝ) : ℝ := iteratedDeriv n (fun x => ising_inverse_square_ring_free_energy L x h) 0 / (n.factorial : ℝ)
