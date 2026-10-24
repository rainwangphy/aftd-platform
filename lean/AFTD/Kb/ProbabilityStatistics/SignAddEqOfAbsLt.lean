import AFTD.Prelude

/-!
# sign_add_eq_of_abs_lt

Topic: concentration   Node: df81bb76a496

Provenance: formalization of a published result. Source: scout/2610-16830-the-communication-complexity-of-the-coin-problem.md:306 Fact 2.1

For any real numbers x and y, if |y| < |x|, then the sign of x + y equals the sign of x.
-/

/-- If |y| < |x|, then sign(x + y) = sign(x). -/
lemma sign_add_eq_of_abs_lt {x y : ℝ} (h : |y| < |x|) :
    SignType.sign (x + y) = SignType.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx] at h
    rw [sign_neg hx, sign_neg]
    linarith [(abs_lt.mp h).1, (abs_lt.mp h).2]
  · subst hx
    have hnon := abs_nonneg y
    simp at h
    linarith
  · rw [abs_of_pos hx] at h
    rw [sign_pos hx, sign_pos]
    linarith [(abs_lt.mp h).1, (abs_lt.mp h).2]
