import AFTD.Prelude

/-!
# energy_filter_lattice_s4

Topic: statistical_mechanics   Node: a06813d17472

Provenance: original. Related work: arXiv:2405.02158

The discrete lattice fourth-moment convolution sum S_4(tau, h) = sum_{m in Z} (sum_{k in Z} exp(-tau^2 h^2 k^2) exp(-tau^2 h^2 (m-k)^2))^2.
-/

/-- Discrete lattice fourth-moment convolution sum S_4(tau, h). -/
noncomputable def energy_filter_lattice_s4 (τ h : ℝ) : ℝ := ∑' (m : ℤ),
    (∑' (k : ℤ), Real.exp (- τ^2 * h^2 * (k : ℝ)^2) *
      Real.exp (- τ^2 * h^2 * ((m - k : ℤ) : ℝ)^2))^2
