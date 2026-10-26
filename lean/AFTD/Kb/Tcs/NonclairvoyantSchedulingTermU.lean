import AFTD.Prelude

/-!
# nonclairvoyant_scheduling_term_U

Topic: online_algorithms   Node: d43e00254d4a

Provenance: formalization of a published result. Source: arXiv:2610.29037 Section C.2 line 3410

The sequence U_i(t) = (2*t*n^2 + (1-t)*i*(2*n+1-i)) / (t*n*(n+1) + (1-t)*i*(i+1)) for n jobs, index i, and parameter t.
-/

/-- The sequence U_i(t) in the robustness upper bound for non-clairvoyant scheduling. -/
noncomputable def nonclairvoyant_scheduling_term_U (n : ℕ) (t : ℝ) (i : ℕ) : ℝ := (2 * t * (n : ℝ)^2 + (1 - t) * (i : ℝ) * (2 * (n : ℝ) + 1 - (i : ℝ))) /
  (t * (n : ℝ) * ((n : ℝ) + 1) + (1 - t) * (i : ℝ) * ((i : ℝ) + 1))
