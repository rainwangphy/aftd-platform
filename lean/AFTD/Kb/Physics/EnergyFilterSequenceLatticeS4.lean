import AFTD.Prelude

/-!
# energy_filter_sequence_lattice_s4

Topic: statistical_mechanics   Node: 7d1736f9fac2

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For a real sequence a on Z, energy_filter_sequence_lattice_s4 a is the sum over m in Z of the squared discrete convolution (sum_{j in Z} a_j a_{m-j})^2.
-/

/-- The fourth-moment convolution sum S_4(a) = sum_{m in Z} (sum_{j in Z} a_j a_{m-j})^2 for a sequence filter a. -/
noncomputable def energy_filter_sequence_lattice_s4 (a : ℤ → ℝ) : ℝ := ∑' m : ℤ, (∑' j : ℤ, a j * a (m - j))^2
