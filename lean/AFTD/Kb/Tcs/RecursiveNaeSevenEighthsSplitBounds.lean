import AFTD.Prelude

/-!
# recursive_nae_seven_eighths_split_bounds

Topic: quantum   Node: 55751d5c562a

Provenance: helper lemma. Balanced split for the recurrence of arXiv:2611.16412, Section 5.2; experiment 27234.

For every depth d at least ten, the rounded seven-eighths split is positive and strictly smaller than d, and the shifted depth decreases by at least a factor 31/32.
-/

theorem recursive_nae_seven_eighths_split_bounds (d : ℕ) (hd : 10 ≤ d) : 1 ≤ (7*d+7)/8 ∧ (7*d+7)/8 < d ∧ 32*((7*d+7)/8+2) ≤ 31*(d+2) := by omega
