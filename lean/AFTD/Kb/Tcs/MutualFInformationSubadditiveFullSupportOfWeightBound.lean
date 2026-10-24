import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFWeight
import AFTD.Kb.Tcs.MutualFInformationSubadditiveFullSupport
import AFTD.Kb.Tcs.MutualFTheta
import AFTD.Kb.Tcs.MutualFThetaConcaveOnOfWeightBound
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.MutualFThetaSelf
import AFTD.Kb.Tcs.MutualFInformationMarkovSubEqSumTheta

/-!
# mutual_f_information_subadditive_full_support_of_weight_bound

Topic: information   Node: 75842244974b

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Theorem 1. Differs: the conclusion is for full-support distributions (the case the proof in Appendix B reduces to), and f is only constrained on (0, ∞) (the paper also asks continuity of f on [0, ∞), which full-support distributions never use).

Theorem 1 of arXiv:2610.21231, on full-support distributions. Let f with f(1) = 0 be convex and four times continuously differentiable on (0, ∞), and g(x) = x² f''(x). If g''(x) < 0 for all x > 0 and there are constants η > 0 and ℓ with g(x) + 2(g'(x) - η)²/(-g''(x)) ≤ 2η + (x - 1)ℓ for all x > 0, then Ĩ_f(X; YZ) ≤ Ĩ_f(X; Y) + Ĩ_f(X; Z) for every full-support Markov chain Y → X → Z on finite sets.
-/

theorem mutual_f_information_subadditive_full_support_of_weight_bound (f : ℝ → ℝ)
    (hf1 : f 1 = 0) (hconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hsmooth : ContDiffOn ℝ 4 f (Set.Ioi 0))
    (hg2 : ∀ x > 0, deriv (deriv (subadditive_f_weight f)) x < 0)
    (hbound : ∃ η ℓ : ℝ, 0 < η ∧ ∀ x > 0,
      subadditive_f_weight f x + 2 * (deriv (subadditive_f_weight f) x - η) ^ 2 /
        (-deriv (deriv (subadditive_f_weight f)) x) ≤ 2 * η + (x - 1) * ℓ) :
    mutual_f_information_subadditive_full_support f := by
  intro X Y Z _ _ _ pX PY PZ hpX hsX hPY hsY hPZ hsZ
  have hdec := mutual_f_information_markov_sub_eq_sum_theta f pX PY PZ hpX hsX hPY hsY hPZ hsZ
  have hcc := mutual_f_theta_concaveOn_of_weight_bound f hf1 hconv hsmooth hg2 hbound
    pX PY hpX hsX hPY hsY
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsX
  set pZ : Z → ℝ := fun z => ∑ x, pX x * PZ x z with hpZ
  have hpZpos : ∀ z, 0 < pZ z := fun z =>
    Finset.sum_pos (fun x _ => mul_pos (hpX x) (hPZ x z)) ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  have hsZ1 : ∑ z, pZ z = 1 := by
    simp only [hpZ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hsZ, mul_one, hsX]
  set rz : Z → X → ℝ := fun z x => pX x * PZ x z / pZ z with hrz
  have hmem : ∀ z ∈ (Finset.univ : Finset Z),
      rz z ∈ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} := by
    intro z _
    refine ⟨fun x => div_pos (mul_pos (hpX x) (hPZ x z)) (hpZpos z), ?_⟩
    simp only [hrz, ← Finset.sum_div]
    exact div_self (hpZpos z).ne'
  have hj := hcc.le_map_sum (t := Finset.univ) (w := pZ) (p := rz)
    (fun z _ => (hpZpos z).le) hsZ1 hmem
  have hsum : ∑ z, pZ z • rz z = pX := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hrz]
    have : ∀ z, pZ z * (pX x * PZ x z / pZ z) = pX x * PZ x z := fun z =>
      mul_div_cancel₀ _ (hpZpos z).ne'
    simp only [this, ← Finset.mul_sum, hsZ, mul_one]
  rw [hsum, mutual_f_theta_self f hf1 pX PY hpX hsY] at hj
  simp only [smul_eq_mul] at hj
  linarith
