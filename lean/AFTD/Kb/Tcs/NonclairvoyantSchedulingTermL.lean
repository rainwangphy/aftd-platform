import AFTD.Prelude

/-!
# nonclairvoyant_scheduling_term_L

Topic: online_algorithms   Node: 2b614e68bf67

Provenance: formalization of a published result. Source: arXiv:2610.29037 Section C.2 line 3473

The lower bound sequence L_s(t) = (s*(2*n+1-s) + 2*t*n*(n-1)) / (s*(s+1) + t*n*(n-1)*(n+s+1)/(n-s+1)) for index s.
-/

/-- The sequence L_s(t) providing a lower bound on the robustness in non-clairvoyant scheduling. -/
noncomputable def nonclairvoyant_scheduling_term_L (n : ℕ) (t : ℝ) (s : ℕ) : ℝ := ((s : ℝ) * (2 * (n : ℝ) + 1 - (s : ℝ)) + 2 * t * (n : ℝ) * ((n : ℝ) - 1)) /
  ((s : ℝ) * ((s : ℝ) + 1) + t * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + (s : ℝ) + 1) / ((n : ℝ) - (s : ℝ) + 1))
