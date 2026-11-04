import AFTD.Prelude

/-!
# gaussian_majority_zeta_constant

Topic: communication   Node: ed402cdb9dbf

Provenance: formalization of a published result. Source: arXiv:2610.16830, The Communication Complexity of the Coin Problem; OP-994

The Gaussian coin majority zeta constant c : ℝ is defined as 7 * (riemannZeta 3).re / π^2.
-/

/-- The asymptotic crossover constant c = 7 * zeta(3) / pi^2 for Gaussian distributed majority. -/
noncomputable def gaussian_majority_zeta_constant : ℝ := 7 * (riemannZeta 3).re / Real.pi ^ 2
