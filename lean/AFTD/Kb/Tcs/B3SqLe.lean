import AFTD.Prelude
import AFTD.Kb.Tcs.B3CoreIneq

/-!
# b3_sq_le

Topic: graphs   Node: b76651942e28

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), proof of Theorem 3.1; serves b3_sqrt_trace_quotient_sq_le_clique_bound

For positive naturals a, b, c with (a, b) ≠ (1, 1): sqrt(a^2 + b^2 - c^2 + 2(a+b+c)c + 3 - 2(a+b+c)) ≤ (a+b+c)(1 - 1/max(a+c, b+c)).
-/

theorem b3_sq_le (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h11 : ¬ (a = 1 ∧ b = 1)) :
    Real.sqrt ((a:ℝ)^2 + b^2 - c^2 + 2*(a+b+c)*c + 3 - 2*(a+b+c))
      ≤ ((a:ℝ)+b+c) * (1 - 1 / ((max (a + c) (b + c) : ℕ) : ℝ)) := by
  rcases le_total b a with hab | hab
  · have h2 : 2 ≤ a := by omega
    have hm : max (a + c) (b + c) = a + c := by omega
    rw [hm]
    have hw : (0:ℝ) < ((a + c : ℕ) : ℝ) := by positivity
    have heq : ((a:ℝ)+b+c) * (1 - 1 / ((a + c : ℕ) : ℝ)) = ((a:ℝ)+b+c) * ((a:ℝ)+c-1) / ((a:ℝ)+c) := by
      push_cast; field_simp
    rw [heq]
    apply Real.sqrt_le_iff.2
    have hw' : (0:ℝ) < (a:ℝ) + c := by push_cast at hw; exact hw
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast h2
    refine ⟨by apply div_nonneg <;> nlinarith, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity), mul_pow]
    exact b3_core_ineq a b c hb hc hab h2
  · have h2 : 2 ≤ b := by omega
    have hm : max (a + c) (b + c) = b + c := by omega
    rw [hm]
    have hw : (0:ℝ) < ((b + c : ℕ) : ℝ) := by positivity
    have heq : ((a:ℝ)+b+c) * (1 - 1 / ((b + c : ℕ) : ℝ)) = ((b:ℝ)+a+c) * ((b:ℝ)+c-1) / ((b:ℝ)+c) := by
      push_cast; field_simp; ring
    rw [heq]
    apply Real.sqrt_le_iff.2
    have hw' : (0:ℝ) < (b:ℝ) + c := by push_cast at hw; exact hw
    have hb' : (2:ℝ) ≤ b := by exact_mod_cast h2
    refine ⟨by apply div_nonneg <;> nlinarith, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity), mul_pow]
    have := b3_core_ineq b a c ha hc hab h2
    nlinarith [this]
