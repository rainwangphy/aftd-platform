import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator
import AFTD.Kb.Tcs.SubadditiveFGeneratorHasDerivAt

/-!
# subadditive_f_generator_contDiffOn

Topic: information   Node: 8975fdda0d4b

Provenance: helper lemma. helper for arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1: the smoothness hypothesis of Theorem 1

If s is twice continuously differentiable on (0, ∞), then the generator f of equation (4) is four times continuously differentiable on (0, ∞).
-/

theorem subadditive_f_generator_contDiffOn (α : ℝ) (s : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 s (Set.Ioi 0)) :
    ContDiffOn ℝ 4 (subadditive_f_generator α s) (Set.Ioi 0) := by
  have hc : ContinuousOn s (Set.Ioi 0) := hs.continuousOn
  have hA2 : ContDiffOn ℝ 2 (fun t => s t / t ^ 2) (Set.Ioi 0) :=
    hs.div (contDiffOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt ht))
  have hAd : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x => ∫ t in (1 : ℝ)..x, s t / t ^ 2) (s y / y ^ 2) y := by
    intro y hy
    have hA : ContinuousOn (fun t => s t / t ^ 2) (Set.Ioi 0) := hA2.continuousOn
    have sub : Set.uIcc 1 y ⊆ Set.Ioi 0 := by
      intro t ht
      rcases Set.mem_uIcc.1 ht with h | h
      · exact lt_of_lt_of_le one_pos h.1
      · exact lt_of_lt_of_le (show (0:ℝ) < y from hy) h.1
    exact intervalIntegral.integral_hasDerivAt_right ((hA.mono sub).intervalIntegrable)
      (hA.stronglyMeasurableAtFilter isOpen_Ioi y hy)
      (hA.continuousAt (isOpen_Ioi.mem_nhds hy))
  have hA3 : ContDiffOn ℝ 3 (fun x => ∫ t in (1 : ℝ)..x, s t / t ^ 2) (Set.Ioi 0) := by
    rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hAd y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hA2.congr (fun y hy => (hAd y hy).deriv)
  have hD : ContDiffOn ℝ 3
      (fun x => α * (Real.log x + 1) + ∫ t in (1 : ℝ)..x, s t / t ^ 2) (Set.Ioi 0) := by
    refine (contDiffOn_const.mul ((Real.contDiffOn_log.mono ?_).add contDiffOn_const)).add hA3
    intro t ht; exact ne_of_gt ht
  rw [show (4 : WithTop ℕ∞) = 3 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (subadditive_f_generator_hasDerivAt α s hc hy).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact hD.congr (fun y hy => (subadditive_f_generator_hasDerivAt α s hc hy).deriv)
