import AFTD.Prelude

/-!
# energy_filter_sequence_lattice_s2

Topic: statistical_mechanics   Node: d1a734462bbf

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For a real sequence a on Z, energy_filter_sequence_lattice_s2 a is the sum of (a j)^2 over all j in Z.
-/

/-- The discrete lattice sum S_2(a) = sum_{j in Z} a_j^2 for a sequence filter a. -/
noncomputable def energy_filter_sequence_lattice_s2 (a : ℤ → ℝ) : ℝ := ∑' j : ℤ, (a j)^2
