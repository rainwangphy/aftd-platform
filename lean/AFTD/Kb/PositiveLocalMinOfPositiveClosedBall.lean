import AFTD.Prelude

/-!
# positive_local_min_of_positive_closed_ball

Topic: analysis   Node: 4b3a620f7bf0

Provenance: helper lemma.

A continuous real function on a proper normed group has a positive local minimum inside a ball if it is positive throughout the closed ball and its boundary values all exceed its value at the center.
-/

open Set Metric

theorem positive_local_min_of_positive_closed_ball
    (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (f : E → ℝ) (r : ℝ) (hr : 0 < r) (hf : Continuous f)
    (hboundary : ∀ x, ‖x‖ = r → f 0 < f x)
    (hpositive : ∀ x, ‖x‖ ≤ r → 0 < f x) :
    ∃ x, ‖x‖ < r ∧ IsLocalMin f x ∧ 0 < f x := by
  have hne : (closedBall (0 : E) r).Nonempty := ⟨0, by simpa using hr.le⟩
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : E) r).exists_isMinOn hne hf.continuousOn
  have hxle : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
  have hxlt : ‖x‖ < r := by
    by_contra hn
    have heq : ‖x‖ = r := le_antisymm hxle (le_of_not_gt hn)
    have h0 : f x ≤ f 0 := hmin (by simpa using hr.le)
    exact (not_lt_of_ge h0) (hboundary x heq)
  refine ⟨x, hxlt, ?_, hpositive x hxle⟩
  apply hmin.isLocalMin
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa [mem_ball, dist_zero_right] using hxlt)) ball_subset_closedBall
