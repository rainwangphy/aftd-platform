import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator
import AFTD.Kb.Tcs.SubadditiveFKs
import AFTD.Kb.Tcs.MutualFInformationSubadditiveFullSupport
import AFTD.Kb.Tcs.MutualFInformationSubadditiveFullSupportOfWeightBound
import AFTD.Kb.Tcs.SubadditiveFGeneratorSatisfiesWeightBound
import AFTD.Kb.Tcs.SubadditiveFWeight

/-!
# subadditive_mutual_f_information_family_full_support

Topic: information   Node: f3bbfc8ec1cf

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1. Differs: subadditivity is stated for full-support distributions; on all distributions it cannot be stated with a real-valued f, since f(0) = ∫_0^1 s(t)/t dt = +∞ whenever s(0+) > 0 (Lean's junk value 0 there makes the all-distributions statement false, e.g. for s = 1 + √x, α = 4: experiment #3380). s is assumed C² on (0, ∞), implicit in the paper.

Corollary 1 of arXiv:2610.21231, on full-support distributions: let s be twice continuously differentiable, positive and concave on (0, ∞) with s'' < 0, let K_s(x) = s(x) + 2(s'(x))²/(-s''(x)) be concave on (0, ∞), and let α ≥ K_s(1). Then f(x) = α x log x + ∫_1^x (x - t) s(t)/t² dt is convex on (0, ∞), f(1) = 0, and Ĩ_f(X; YZ) ≤ Ĩ_f(X; Y) + Ĩ_f(X; Z) for every full-support Markov chain Y → X → Z on finite sets.
-/

theorem subadditive_mutual_f_information_family_full_support (s : ℝ → ℝ) (α : ℝ)
    (hs_smooth : ContDiffOn ℝ 2 s (Set.Ioi 0))
    (hs_pos : ∀ x > 0, 0 < s x)
    (hs_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) s)
    (hs_deriv2_neg : ∀ x > 0, deriv (deriv s) x < 0)
    (hKs_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (subadditive_f_ks s))
    (hα : subadditive_f_ks s 1 ≤ α) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (subadditive_f_generator α s) ∧
      subadditive_f_generator α s 1 = 0 ∧
      mutual_f_information_subadditive_full_support (subadditive_f_generator α s) := by
  obtain ⟨hconv, hf1, hsmooth4, hg2, hbound⟩ :=
    subadditive_f_generator_satisfies_weight_bound s α hs_smooth hs_pos hs_deriv2_neg hKs_concave hα
  exact ⟨hconv, hf1,
    mutual_f_information_subadditive_full_support_of_weight_bound _
      hf1 hconv hsmooth4 hg2 hbound⟩
