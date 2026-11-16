import AFTD.Prelude
import AFTD.Kb.Tcs.AdditiveNoiseSuccessProb

/-!
# constant_decision_rule_success_prob

Topic: information   Node: 64079b1de6c0

Provenance: helper lemma. arXiv:2611.16066 Proposition 3.1 proof -- Optimal Additive Integer Masks for One-Guess Vulnerability under an Absolute-Moment Budget

For any secret distribution p on Fin m and probability distribution q on ℤ with sum 1, the constant decision rule guessing x₀ for all observations s achieves average success probability p(x₀).
-/

/-- The constant decision rule guessing x₀ achieves success probability p(x₀). -/
lemma constant_decision_rule_success_prob (m : ℕ) (p : Fin m → ℝ) (q : ℤ → ℝ) (hq_sum : HasSum q 1) (x₀ : Fin m) : additive_noise_success_prob m p q (fun _ => x₀) = p x₀ := by
  unfold additive_noise_success_prob
  simp only
  have hqshift : HasSum (fun s : ℤ => q (s - ((x₀ : ℕ) : ℤ))) 1 := by
    have h :=
      (Equiv.hasSum_iff (f := q) (a := 1)
        (e := Equiv.subRight (((x₀ : ℕ) : ℤ)))).2 hq_sum
    convert h using 1
    · ext s
      simp [Equiv.subRight_apply]
  rw [tsum_mul_left, hqshift.tsum_eq, mul_one]
