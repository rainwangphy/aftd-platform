import AFTD.Prelude
import AFTD.Kb.Tcs.PaymentWindow

/-!
# payment_window_amortized_bound

Topic: online_algorithms   Node: 87a8a12c5b63

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.2, Lemma 3.4

For any page type α, any natural number k, and any payment window w : PaymentWindow α k, the offline cost covers the online payment and potential change: 1 ≤ (k + 1 : ℝ) * (w.delta_fetches_opt : ℝ) + (k + 1 : ℝ) * w.delta_delay_opt - (w.delta_phi : ℝ).
-/

/-- Amortized charge inequality for each payment window. -/
theorem payment_window_amortized_bound {α : Type*} (k : ℕ) (w : PaymentWindow α k) : 1 ≤ (k + 1 : ℝ) * (w.delta_fetches_opt : ℝ) + (k + 1 : ℝ) * w.delta_delay_opt - (w.delta_phi : ℝ) := by
  have hd : 0 ≤ w.delta_delay_opt := w.delta_delay_nonneg
  have hf : (0 : ℝ) ≤ (w.delta_fetches_opt : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  rcases w.case_condition with h | ⟨hf1, hφ⟩ | ⟨hd1, hφ⟩
  · have h' : (w.delta_phi : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith
  · have hφ' : (w.delta_phi : ℝ) ≤ (k : ℝ) := by exact_mod_cast hφ
    have hf1' : (1 : ℝ) ≤ (w.delta_fetches_opt : ℝ) := by exact_mod_cast hf1
    nlinarith
  · have hφ' : (w.delta_phi : ℝ) ≤ (k : ℝ) := by exact_mod_cast hφ
    have hd1' : (1 : ℝ) ≤ w.delta_delay_opt := by exact_mod_cast hd1
    nlinarith
