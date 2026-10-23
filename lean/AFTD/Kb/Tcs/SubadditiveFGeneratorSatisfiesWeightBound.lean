import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator
import AFTD.Kb.Tcs.SubadditiveFKs
import AFTD.Kb.Tcs.SubadditiveFWeight
import AFTD.Kb.Tcs.SubadditiveKsIdentity
import AFTD.Kb.Tcs.SubadditiveTangentBoundStep
import AFTD.Kb.Tcs.ConcaveOnIoiExistsSupergradientAtOne
import AFTD.Kb.Tcs.SubadditiveFGeneratorHasDerivAt
import AFTD.Kb.Tcs.SubadditiveFGeneratorDeriv2
import AFTD.Kb.Tcs.SubadditiveFGeneratorContDiffOn
import AFTD.Kb.Tcs.SubadditiveFGeneratorWeightEventuallyEq

/-!
# subadditive_f_generator_satisfies_weight_bound

Topic: information   Node: 8e8f131e60ed

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1 (the claim that g satisfies the assumptions of Theorem 1, Appendix C). Differs: s is assumed C² on (0, ∞), which the paper leaves implicit (it needs s'' and Theorem 1 needs f ∈ C⁴); ℓ uses a one-sided derivative of the concave K_s at 1 instead of K_s'(1).

First claim of Corollary 1 of arXiv:2610.21231: let s be twice continuously differentiable and positive on (0, ∞) with s'' < 0, let K_s(x) = s(x) + 2(s'(x))²/(-s''(x)) be concave on (0, ∞), and α ≥ K_s(1). Then the generator f(x) = α x log x + ∫_1^x (x - t) s(t)/t² dt satisfies the hypotheses of Theorem 1: f is convex and C⁴ on (0, ∞), f(1) = 0, g = x² f'' = α x + s has g'' < 0, and g(x) + 2(g'(x) - η)²/(-g''(x)) ≤ 2η + (x - 1)ℓ for all x > 0, with η = α and ℓ = α + (a supergradient of K_s at 1).
-/

theorem subadditive_f_generator_satisfies_weight_bound (s : ℝ → ℝ) (α : ℝ)
    (hs_smooth : ContDiffOn ℝ 2 s (Set.Ioi 0))
    (hs_pos : ∀ x > 0, 0 < s x)
    (hs_deriv2_neg : ∀ x > 0, deriv (deriv s) x < 0)
    (hKs_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (subadditive_f_ks s))
    (hα : subadditive_f_ks s 1 ≤ α) :
    ConvexOn ℝ (Set.Ioi 0) (subadditive_f_generator α s) ∧
      subadditive_f_generator α s 1 = 0 ∧
      ContDiffOn ℝ 4 (subadditive_f_generator α s) (Set.Ioi 0) ∧
      (∀ x > 0, deriv (deriv (subadditive_f_weight (subadditive_f_generator α s))) x < 0) ∧
      ∃ η ℓ : ℝ, 0 < η ∧ ∀ x > 0,
        subadditive_f_weight (subadditive_f_generator α s) x +
          2 * (deriv (subadditive_f_weight (subadditive_f_generator α s)) x - η) ^ 2 /
            (-deriv (deriv (subadditive_f_weight (subadditive_f_generator α s))) x) ≤
          2 * η + (x - 1) * ℓ := by
  have hc : ContinuousOn s (Set.Ioi 0) := hs_smooth.continuousOn
  have hα_pos : 0 < α := by
    refine lt_of_lt_of_le ?_ hα
    unfold subadditive_f_ks
    have h1 := hs_pos 1 one_pos
    have h2 := div_nonneg (by positivity : (0 : ℝ) ≤ 2 * deriv s 1 ^ 2)
      (neg_pos.mpr (hs_deriv2_neg 1 one_pos)).le
    linarith
  have hsd : ∀ y > 0, DifferentiableAt ℝ s y := fun y hy =>
    (hs_smooth.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
  -- derivatives of the weight g = x² f'' = α x + s x
  have hg1 : ∀ x > 0, deriv (subadditive_f_weight (subadditive_f_generator α s)) =ᶠ[nhds x]
      fun y => α + deriv s y := by
    intro x hx
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [(subadditive_f_generator_weight_eventuallyEq α s hc hy).deriv_eq]
    exact (((hasDerivAt_id y).const_mul α).add (hsd y hy).hasDerivAt).deriv.trans (by simp)
  have hg2 : ∀ x > 0,
      deriv (deriv (subadditive_f_weight (subadditive_f_generator α s))) x = deriv (deriv s) x := by
    intro x hx
    rw [(hg1 x hx).deriv_eq]
    exact deriv_const_add α
  refine ⟨?_, by simp [subadditive_f_generator], subadditive_f_generator_contDiffOn α s hs_smooth,
    fun x hx => (hg2 x hx).symm ▸ hs_deriv2_neg x hx, ?_⟩
  · refine convexOn_of_deriv2_nonneg' (convex_Ioi 0)
      (fun y hy => (subadditive_f_generator_hasDerivAt α s hc hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (subadditive_f_generator_deriv2 α s hc hy).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    rw [Function.iterate_succ_apply, Function.iterate_one, (subadditive_f_generator_deriv2 α s hc hy').deriv]
    have := hs_pos y hy'
    positivity
  · obtain ⟨ℓK, hℓK⟩ := concave_on_ioi_exists_supergradient_at_one hKs_concave
    refine ⟨α, α + ℓK, hα_pos, fun x hx => ?_⟩
    have hid := subadditive_ks_identity α x s (subadditive_f_weight (subadditive_f_generator α s))
      (subadditive_f_generator_weight_eventuallyEq α s hc hx).eq_of_nhds
      (by rw [(hg1 x hx).eq_of_nhds]; ring) (hg2 x hx)
    rw [hid]
    exact subadditive_tangent_bound_step α (α + ℓK) _ ℓK x _ rfl hα (by linarith [hℓK x hx])
