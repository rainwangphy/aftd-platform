import AFTD.Prelude
import AFTD.Kb.Tcs.WordAsymptoticCriticalExponent
import AFTD.Kb.Tcs.WordCriticalExponent

/-!
# op_1458_asymptotic_critical_exponent_le_critical_exponent

Topic: combinatorics   Node: 0cac31f5daff

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1

For every infinite word w, the asymptotic critical exponent of w is at most the critical exponent of w in ℝ.
-/

lemma op_1458_asymptotic_critical_exponent_le_critical_exponent_sSup_nonneg
    {T : Set ℝ} (h0 : (0 : ℝ) ∈ T) : 0 ≤ sSup T := by
  by_cases h : BddAbove T
  · exact le_csSup h h0
  · rw [Real.sSup_of_not_bddAbove h]

lemma op_1458_asymptotic_critical_exponent_le_critical_exponent_zero_mem
    {α : Type*} (w : ℕ → α) (N : ℕ) (hN : 1 ≤ N) :
    (0 : ℝ) ∈ { e : ℝ | ∃ (x y : List α) (m : ℕ), x ≠ [] ∧ N ≤ x.length ∧
      (∃ i : ℕ, y = (List.range y.length).map (fun j => w (i + j))) ∧
      y <+: (List.replicate m x).flatten ∧ e = (y.length : ℝ) / (x.length : ℝ) } := by
  refine ⟨List.replicate N (w 0), [], 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : (List.replicate N (w 0)).length = 0 := by rw [h, List.length_nil]
    rw [List.length_replicate] at this
    omega
  · simp
  · refine ⟨0, ?_⟩
    simp
  · exact List.nil_prefix
  · simp

/-- The asymptotic critical exponent is bounded from above by the critical exponent. -/
theorem op_1458_asymptotic_critical_exponent_le_critical_exponent {α : Type*} (w : ℕ → α) :
    word_asymptotic_critical_exponent w ≤ word_critical_exponent w := by
  unfold word_asymptotic_critical_exponent word_critical_exponent
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨N, hN, rfl⟩
    exact op_1458_asymptotic_critical_exponent_le_critical_exponent_sSup_nonneg
      (op_1458_asymptotic_critical_exponent_le_critical_exponent_zero_mem w N hN)
  · refine ⟨1, le_rfl, ?_⟩
    congr 1
    ext e
    constructor
    · rintro ⟨x, y, m, hx, hy, hpref, he⟩
      have h1 : 1 ≤ x.length := by
        cases x
        · contradiction
        · simp
      exact ⟨x, y, m, hx, h1, hy, hpref, he⟩
    · rintro ⟨x, y, m, hx, h1, hy, hpref, he⟩
      exact ⟨x, y, m, hx, hy, hpref, he⟩
