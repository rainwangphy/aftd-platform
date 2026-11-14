import AFTD.Prelude
import AFTD.Kb.Tcs.ExactQuantumQueryComplexity
import AFTD.Kb.Tcs.RecursiveNae

/-!
# recursive_nae_contractive_normalized_recurrence_implies_upper_bound

Topic: quantum   Node: fc8e2fc573b6

Provenance: helper lemma. arXiv:2611.16412, Problem 12.2, fixed-depth recurrence implication

If a positive fixed depth b and constants 0 ≤ θ < 1 and K ≥ 0 give a recurrence u(k+b) ≤ θu(k)+K for every k, where u(k) is the exact quantum query complexity of recursive ternary NAE at depth k divided by (3/√2)^k, then these query complexities are at most C(3/√2)^k for all k ≥ 1 for a positive constant C.
-/

theorem recursive_nae_contractive_normalized_recurrence_implies_upper_bound (b : ℕ) (hb : 0 < b) (θ K : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hK : 0 ≤ K)
    (hrec : ∀ k : ℕ,
      (exact_quantum_query_complexity (recursive_nae (k + b)) : ℝ) /
        (3 / Real.sqrt 2) ^ (k + b) ≤
      θ * ((exact_quantum_query_complexity (recursive_nae k) : ℝ) /
        (3 / Real.sqrt 2) ^ k) + K) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      (exact_quantum_query_complexity (recursive_nae k) : ℝ) ≤
        C * (3 / Real.sqrt 2) ^ k := by
  let a : ℝ := 3 / Real.sqrt 2
  have ha : 0 < a := by dsimp [a]; positivity
  let u : ℕ → ℝ := fun k => (exact_quantum_query_complexity (recursive_nae k) : ℝ) / a ^ k
  let M : ℝ := (Finset.range b).sup' (⟨0, Finset.mem_range.mpr hb⟩) u
  let C : ℝ := max M (K / (1 - θ)) + 1
  have hCp : 0 < C := by
    have : 0 ≤ K / (1 - θ) := div_nonneg hK (le_of_lt (sub_pos.mpr hθ₁))
    dsimp [C]; linarith [le_max_right M (K / (1 - θ))]
  have hbound : ∀ n, u n ≤ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < b
      · have hM : u n ≤ M := Finset.le_sup' u (Finset.mem_range.mpr hn)
        dsimp [C]; linarith [le_max_left M (K / (1 - θ))]
      · have hbn : b ≤ n := Nat.le_of_not_gt hn
        have hlt : n - b < n := Nat.sub_lt (by omega) hb
        have hind := ih (n - b) hlt
        have hr := hrec (n - b)
        have hrel : u n ≤ θ * u (n - b) + K := by
          rw [Nat.sub_add_cancel hbn] at hr
          simpa [u, a] using hr
        have hKC : K ≤ (1 - θ) * C := by
          have hh : K / (1 - θ) ≤ C := by dsimp [C]; linarith [le_max_right M (K / (1 - θ))]
          simpa [mul_comm] using (div_le_iff₀ (sub_pos.mpr hθ₁)).mp hh
        nlinarith [mul_nonneg hθ₀ (sub_nonneg.mpr hind)]
  refine ⟨C, hCp, ?_⟩
  intro k hk
  have hh := hbound k
  have hkpos : 0 < a ^ k := pow_pos ha k
  exact (div_le_iff₀ hkpos).mp hh
