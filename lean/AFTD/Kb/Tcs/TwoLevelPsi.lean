import AFTD.Prelude

/-!
# two_level_psi

Topic: quantum   Node: d056dfdf86fb

Provenance: helper lemma. step towards prime_convolution_entanglement_breaking_iff_threshold

The unit vector psi_p on Fin d with psi_p(j) = sqrt(p) for j = 0, sqrt(1 - p) for j = 1, and 0 for all other j (the pure state entering the two-level environment).
-/

/-- Vector with entries sqrt p at index 0, sqrt (1 - p) at index 1 and 0 elsewhere; the pure state of the two-level environment. -/
noncomputable def two_level_psi (d : ℕ) (p : ℝ) : Fin d → ℝ := fun j => if (j : ℕ) = 0 then Real.sqrt p else if (j : ℕ) = 1 then Real.sqrt (1 - p) else 0
