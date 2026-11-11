import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesFiber15Form

/-!
# good_slopes_fiber15_anchored_rigidity

Topic: elementary_number_theory   Node: 3dfcc502e7b8

Provenance: helper lemma. Normalized four-direction rigidity used in the fiber analysis of OP-1027; arXiv:2611.04551, Question 10.2.

Let S be a set of points over the residues modulo 15 containing (0,0) and (1,14). If the form y+4x is surjective on S, and the forms y+7x, y+11x and y+13x are each injective on S, then this is impossible.
-/

private theorem good_slopes_fiber15_force_six : ∀ p : ZMod 15 × ZMod 15,
    good_slopes_fiber15_form 4 p = 6 →
    good_slopes_fiber15_form 7 p ≠ 0 → good_slopes_fiber15_form 7 p ≠ 6 →
    good_slopes_fiber15_form 13 p ≠ 0 → good_slopes_fiber15_form 13 p ≠ 12 →
    good_slopes_fiber15_form 11 p ≠ 0 → good_slopes_fiber15_form 11 p ≠ 10 →
    p = (2, 13) := by decide

private theorem good_slopes_fiber15_force_twelve : ∀ p : ZMod 15 × ZMod 15,
    good_slopes_fiber15_form 4 p = 12 →
    good_slopes_fiber15_form 7 p ≠ 0 → good_slopes_fiber15_form 7 p ≠ 6 →
    good_slopes_fiber15_form 13 p ≠ 0 → good_slopes_fiber15_form 13 p ≠ 12 →
    good_slopes_fiber15_form 11 p ≠ 0 → good_slopes_fiber15_form 11 p ≠ 10 →
    p = (14, 1) := by decide

theorem good_slopes_fiber15_anchored_rigidity (S : Set (ZMod 15 × ZMod 15))
    (h0 : (0, 0) ∈ S) (h1 : (1, 14) ∈ S)
    (h4 : ∀ t, ∃ p ∈ S, good_slopes_fiber15_form 4 p = t)
    (h7 : Set.InjOn (good_slopes_fiber15_form 7) S)
    (h11 : Set.InjOn (good_slopes_fiber15_form 11) S)
    (h13 : Set.InjOn (good_slopes_fiber15_form 13) S) : False := by
  obtain ⟨p, hp, hp4⟩ := h4 6
  obtain ⟨q, hq, hq4⟩ := h4 12
  have p0 : p ≠ (0, 0) := by
    intro h; subst p; revert hp4; decide
  have p1 : p ≠ (1, 14) := by
    intro h; subst p; revert hp4; decide
  have q0 : q ≠ (0, 0) := by
    intro h; subst q; revert hq4; decide
  have q1 : q ≠ (1, 14) := by
    intro h; subst q; revert hq4; decide
  have hp7a : good_slopes_fiber15_form 7 p ≠ 0 := by
    intro h; apply p0; apply h7 hp h0; simpa [good_slopes_fiber15_form] using h
  have hp7b : good_slopes_fiber15_form 7 p ≠ 6 := by
    intro h; apply p1; apply h7 hp h1; simpa only [show good_slopes_fiber15_form 7 (1, 14) = 6 by decide] using h
  have hp13a : good_slopes_fiber15_form 13 p ≠ 0 := by
    intro h; apply p0; apply h13 hp h0; simpa [good_slopes_fiber15_form] using h
  have hp13b : good_slopes_fiber15_form 13 p ≠ 12 := by
    intro h; apply p1; apply h13 hp h1; simpa only [show good_slopes_fiber15_form 13 (1, 14) = 12 by decide] using h
  have hp11a : good_slopes_fiber15_form 11 p ≠ 0 := by
    intro h; apply p0; apply h11 hp h0; simpa [good_slopes_fiber15_form] using h
  have hp11b : good_slopes_fiber15_form 11 p ≠ 10 := by
    intro h; apply p1; apply h11 hp h1; simpa only [show good_slopes_fiber15_form 11 (1, 14) = 10 by decide] using h
  have hq7a : good_slopes_fiber15_form 7 q ≠ 0 := by
    intro h; apply q0; apply h7 hq h0; simpa [good_slopes_fiber15_form] using h
  have hq7b : good_slopes_fiber15_form 7 q ≠ 6 := by
    intro h; apply q1; apply h7 hq h1; simpa only [show good_slopes_fiber15_form 7 (1, 14) = 6 by decide] using h
  have hq13a : good_slopes_fiber15_form 13 q ≠ 0 := by
    intro h; apply q0; apply h13 hq h0; simpa [good_slopes_fiber15_form] using h
  have hq13b : good_slopes_fiber15_form 13 q ≠ 12 := by
    intro h; apply q1; apply h13 hq h1; simpa only [show good_slopes_fiber15_form 13 (1, 14) = 12 by decide] using h
  have hq11a : good_slopes_fiber15_form 11 q ≠ 0 := by
    intro h; apply q0; apply h11 hq h0; simpa [good_slopes_fiber15_form] using h
  have hq11b : good_slopes_fiber15_form 11 q ≠ 10 := by
    intro h; apply q1; apply h11 hq h1; simpa only [show good_slopes_fiber15_form 11 (1, 14) = 10 by decide] using h
  have hpf := good_slopes_fiber15_force_six p hp4 hp7a hp7b hp13a hp13b hp11a hp11b
  have hqf := good_slopes_fiber15_force_twelve q hq4 hq7a hq7b hq13a hq13b hq11a hq11b
  have heq : good_slopes_fiber15_form 11 p = good_slopes_fiber15_form 11 q := by
    rw [hpf, hqf]; decide
  have hpq := h11 hp hq heq
  rw [hpf, hqf] at hpq
  revert hpq
  decide
