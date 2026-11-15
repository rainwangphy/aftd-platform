import AFTD.Prelude

/-!
# rare_tail_target_limit_lt_one

Topic: combinatorics   Node: 5c385a4229f1

Provenance: helper lemma. arXiv:2106.02330, OP-1721

For every real p strictly between 0 and 1, the rare-tail limit ratio 4 * (1 - p) / (1 + (1 - p))^2 is strictly less than 1.
-/

/-- The asymptotic matching-ratio limit 4q/(1+q)^2 is strictly less than 1 for all p in (0, 1) -/
theorem rare_tail_target_limit_lt_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    4 * (1 - p) / (1 + (1 - p)) ^ 2 < 1 := by
  have h_pos : 0 < (1 + (1 - p)) ^ 2 := by positivity
  rw [div_lt_iff₀ h_pos]
  nlinarith [sq_nonneg p]
