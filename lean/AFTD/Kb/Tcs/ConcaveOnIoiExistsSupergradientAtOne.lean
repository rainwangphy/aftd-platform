import AFTD.Prelude

/-!
# concave_on_ioi_exists_supergradient_at_one

Topic: information   Node: 041dc81405a5

Provenance: helper lemma. helper for arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1 (Appendix C, first-order inequality for the concave K_s)

A function K concave on (0, ∞) has a supergradient at 1: there is ℓ with K(x) ≤ K(1) + ℓ (x - 1) for all x > 0 (the first-order inequality K_s(x) ≤ K_s(1) + K_s'(1)(x - 1) of Appendix C, with a one-sided derivative in place of K_s'(1)).
-/

theorem concave_on_ioi_exists_supergradient_at_one {K : ℝ → ℝ}
    (hK : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) K) :
    ∃ ℓ : ℝ, ∀ x > 0, K x ≤ K 1 + ℓ * (x - 1) := by
  have hF : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -K x) := hK.neg
  have h1 : (1 : ℝ) ∈ interior (Set.Ioi (0 : ℝ)) := by
    rw [interior_Ioi]; norm_num
  refine ⟨-derivWithin (fun x => -K x) (Set.Ioi 1) 1, fun x hx => ?_⟩
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have h := (hF.slope_le_leftDeriv_of_mem_interior hx h1 hlt).trans
      (hF.leftDeriv_le_rightDeriv_of_mem_interior h1)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    nlinarith
  · subst heq; simp
  · have h := hF.rightDeriv_le_slope_of_mem_interior h1 (show x ∈ Set.Ioi (0:ℝ) from hx) hgt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    nlinarith
