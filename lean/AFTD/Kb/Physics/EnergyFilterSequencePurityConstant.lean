import AFTD.Prelude

/-!
# energy_filter_sequence_purity_constant

Topic: statistical_mechanics   Node: 24322f9837e6

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For a real sequence a on Z, energy_filter_sequence_purity_constant a is (2 / sqrt(pi)) times the ratio of the fourth-moment convolution sum S_4(a) to the square of the second-moment sum S_2(a)^2.
-/

/-- The universal asymptotic purity prefactor C(a) = (2/sqrt(pi)) S_4(a) / S_2(a)^2 for a sequence filter a. -/
noncomputable def energy_filter_sequence_purity_constant (a : ℤ → ℝ) : ℝ := (2 / Real.sqrt Real.pi) * (∑' m : ℤ, (∑' j : ℤ, a j * a (m - j))^2) /
    (∑' j : ℤ, (a j)^2)^2
