import AFTD.Prelude
import AFTD.Kb.Tcs.HasDepthThreeAmcProof
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.HasDepthThreeAmcBoundedBiasProof
import AFTD.Kb.Tcs.IsDnfTautology

/-!
# depth_three_amc_separation_from_asymptotic_family

Topic: proof_complexity   Node: b35695357da0

Provenance: helper lemma. step towards op_983_depth_three_amc_separation_at_constant_shift

Any asymptotic family of DNF formulas satisfying the AMC upper bound and bounded-bias lower bound for k ≥ k₀ extends to a full family satisfying the separation theorem, using AMC soundness to establish tautology for k ≥ k₀ and padding with the empty clause for k < k₀.
-/

/-- Given an asymptotic family separating depth-three AMC from bounded-bias AMC for k ≥ k₀, one can extend it to all k by padding small k with the empty clause [[]] and applying soundness for k ≥ k₀. -/
theorem depth_three_amc_separation_from_asymptotic_family
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1)
    (v : ℕ → ℕ) (hv : ∀ k, k ≤ v k)
    (A : (k : ℕ) → List (List (CnfLit (Fin (v k)))))
    (c : ℕ) (k₀ : ℕ)
    (h_ub : ∀ k ≥ k₀, ∃ r ≤ (v k) ^ c + c, has_depth_three_amc_proof (v k) (A k) ε r)
    (h_lb : ∀ c' : ℕ, ∃ k₀' : ℕ, ∀ k ≥ k₀', ∀ s : ℕ, has_depth_three_amc_bounded_bias_proof (v k) (A k) ε s → (v k) ^ c' < s)
    (h_sound : ∀ n (F : List (List (CnfLit (Fin n)))) r, has_depth_three_amc_proof n F ε r → is_dnf_tautology F) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ (v : ℕ → ℕ) (hv : ∀ k, k ≤ v k) (A : (k : ℕ) → List (List (CnfLit (Fin (v k))))),
        (∀ k, is_dnf_tautology (A k)) ∧
        (∃ c : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ r ≤ (v k) ^ c + c, has_depth_three_amc_proof (v k) (A k) ε r) ∧
        (∀ c : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ s : ℕ, has_depth_three_amc_bounded_bias_proof (v k) (A k) ε s → (v k) ^ c < s) := by
  refine ⟨ε, hε_pos, hε_le, v, hv, fun k => if k < k₀ then [[]] else A k, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k < k₀
    · simp only [hk, if_true]
      intro τ; exact ⟨[], by simp, by simp⟩
    · simp only [hk, if_false]
      obtain ⟨r, _, hr⟩ := h_ub k (Nat.le_of_not_lt hk)
      exact h_sound (v k) (A k) r hr
  · refine ⟨c, k₀, ?_⟩
    intro k hk
    obtain ⟨r, hr, hp⟩ := h_ub k hk
    exact ⟨r, hr, by simpa [Nat.not_lt.mpr hk] using hp⟩
  · intro c'
    obtain ⟨k₀', hk'⟩ := h_lb c'
    refine ⟨max k₀' k₀, ?_⟩
    intro k hk s hs
    have h1 : k₀' ≤ k := le_trans (le_max_left _ _) hk
    have h2 : k₀ ≤ k := le_trans (le_max_right _ _) hk
    have hA : (if k < k₀ then [[]] else A k) = A k := by simp [Nat.not_lt.mpr h2]
    simp only [hA] at hs
    exact hk' k h1 s hs
