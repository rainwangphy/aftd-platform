import AFTD.Prelude

/-!
# asymptotics_isLittleO_of_pos_neg

Topic: fair_division   Node: a5f05b10eab3

Provenance: helper lemma. step towards mms_threshold_monotone_asymptotic

If both the positive and negative deviations max(0, f(n)) and max(0, -f(n)) are little-o of g(n) along Filter.atTop, then f(n) = o(g(n)).
-/

/-- Real functions f with max 0 f =o[atTop] g and max 0 (-f) =o[atTop] g satisfy f =o[atTop] g. -/
theorem asymptotics_isLittleO_of_pos_neg (f g : ℕ → ℝ)
    (hpos : (fun n => max 0 (f n)) =o[Filter.atTop] g)
    (hneg : (fun n => max 0 (-f n)) =o[Filter.atTop] g) :
    f =o[Filter.atTop] g := by
  refine (hpos.sub hneg).congr_left ?_
  intro n
  rcases le_total 0 (f n) with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h)]
    ring
