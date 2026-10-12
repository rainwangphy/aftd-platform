import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDist
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDistApply
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairApply

/-!
# pmf_output_indist_of_posterior_eq_prior

Topic: randomness   Node: 07aaf5fdc22a

Provenance: formalization of a published result. Source: Shannon (1949), 'Communication Theory of Secrecy Systems', Theorem 1

Let α and β be types, p a PMF on α, and f : α → PMF β a channel. Suppose that for every output b in the support of the marginal distribution (p.bind f), the posterior distribution Cslib.Probability.PMF.posteriorDist p f b hb equals p. Then for all inputs a₀ and a₁ in the support of p, the output distributions f a₀ and f a₁ are equal.
-/

/-- If conditioning on every output in the marginal support leaves the posterior equal to the prior, then the output distributions are identical across all inputs in the support. -/
theorem pmf_output_indist_of_posterior_eq_prior {α β : Type*} (p : PMF α) (f : α → PMF β)
    (h : ∀ (b : β) (hb : b ∈ (p.bind f).support), Cslib.Probability.PMF.posteriorDist p f b hb = p)
    (a₀ a₁ : α) (h₀ : a₀ ∈ p.support) (h₁ : a₁ ∈ p.support) :
    f a₀ = f a₁ := by
  have h_eq : ∀ (a : α), a ∈ p.support → ∀ (b : β), f a b = (p.bind f) b := by
    intro a ha b
    by_cases hb : b ∈ (p.bind f).support
    · have h1 : Cslib.Probability.PMF.posteriorDist p f b hb a = p a := by rw [h b hb]
      rw [Cslib.Probability.PMF.posteriorDist_apply, Cslib.Probability.PMF.bind_pair_apply] at h1
      have hb_ne_zero : (p.bind f) b ≠ 0 := by rwa [PMF.mem_support_iff] at hb
      have hb_ne_top := PMF.apply_ne_top (p.bind f) b
      have ha_ne_zero : p a ≠ 0 := by rwa [PMF.mem_support_iff] at ha
      have ha_ne_top := PMF.apply_ne_top p a
      have h2 : (p a * f a b) / (p.bind f) b * (p.bind f) b = p a * (p.bind f) b := by
        rw [h1]
      rw [ENNReal.div_mul_cancel hb_ne_zero hb_ne_top] at h2
      exact (ENNReal.mul_right_inj ha_ne_zero ha_ne_top).mp h2
    · have hb_zero : (p.bind f) b = 0 := by
        rwa [PMF.mem_support_iff, Classical.not_not] at hb
      rw [hb_zero]
      have h_bind : (p.bind f) b = ∑' a', p a' * f a' b := PMF.bind_apply p f b
      rw [hb_zero] at h_bind
      have h_all : ∀ a', p a' * f a' b = 0 := by
        rwa [← ENNReal.tsum_eq_zero]
      have ha_prod := h_all a
      have ha_ne_zero : p a ≠ 0 := by rwa [PMF.mem_support_iff] at ha
      exact (mul_eq_zero_iff_left ha_ne_zero).mp ha_prod
  ext b
  rw [h_eq a₀ h₀ b, h_eq a₁ h₁ b]
