import AFTD.Prelude
import AFTD.Kb.Tcs.MajorityThree
import AFTD.Kb.Tcs.DictatorDist
import AFTD.Kb.Tcs.HellingerZ
import AFTD.Kb.Tcs.C3
import AFTD.Kb.Tcs.IsSignedDictator

/-!
# not_antipodal_hellinger_majority_three_ratio

Topic: information   Node: 126013e5550c

Provenance: original. Related work: refutes `antipodal_hellinger_majority_three_ratio`

The statement `antipodal_hellinger_majority_three_ratio` is false: The theorem statement claims that dictator_dist 3 majority_three = 1 / 4. However, dictator_dist n f is defined as `⨅ (g : (Fin n → Bool) → ℝ) (_ : is_signed_dictator n g), (1 / (2 : ℝ) ^ n) * ∑ x, if f x ≠ g x then 1 else 0`. On ℝ, `sInf ∅ = 0` (via `Real.sInf_empty`), so for any function g that is not a signed dictator (such as `fun _ => 0`), the inner infimum `⨅ (_ : is_signed_dictator n g), ...` evaluates to `sInf ∅ = 0`. Because every term is non-negative, the outer infimum is bounded above by 0, hence `dictator_dist 3 majority_three ≤ 0 < 1 / 4`. Thus `dictator_dist 3 majority_three = 1 / 4` is false in Lean 4.
-/

theorem not_antipodal_hellinger_majority_three_ratio : ¬ (∀ (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1), dictator_dist 3 majority_three = 1 / 4 ∧
    hellinger_Z 3 ρ majority_three - Real.sqrt (1 - ρ ^ 2) = c_3 ρ * (1 / 4)) := by
  have not_dictator : ¬ is_signed_dictator 3 (fun _ => (0 : ℝ)) := by
    intro ⟨i, s, hs, hg⟩
    have h0 := hg (fun _ => false)
    dsimp at h0
    rcases hs with rfl | rfl <;> linarith
  have my_dist_le_zero : dictator_dist 3 majority_three ≤ 0 := by
    unfold dictator_dist
    have h_range : (⨅ (_ : is_signed_dictator 3 (fun _ => (0 : ℝ))), (1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ (fun _ => (0 : ℝ)) x then 1 else 0) = 0 := by
      have he : (Set.range (fun (_ : is_signed_dictator 3 (fun _ => (0 : ℝ))) => (1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ (fun _ => (0 : ℝ)) x then 1 else 0)) = ∅ := by
        ext y
        simp [not_dictator]
      change sInf _ = 0
      rw [he, Real.sInf_empty]
    have h_bdd : BddBelow (Set.range (fun g => ⨅ (_ : is_signed_dictator 3 g), (1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ g x then 1 else 0)) := by
      use 0
      rintro y ⟨g, rfl⟩
      by_cases hg : is_signed_dictator 3 g
      · have he : (Set.range (fun (_ : is_signed_dictator 3 g) => (1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ g x then 1 else 0)) = {(1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ g x then 1 else 0} := by
          ext z
          simp [hg]
        change 0 ≤ sInf _
        rw [he, csInf_singleton]
        positivity
      · have he : (Set.range (fun (_ : is_signed_dictator 3 g) => (1 / (2 : ℝ) ^ 3) * ∑ x, if majority_three x ≠ g x then 1 else 0)) = ∅ := by
          ext z
          simp [hg]
        change 0 ≤ sInf _
        rw [he, Real.sInf_empty]
    have h_le := ciInf_le h_bdd (fun _ => (0 : ℝ))
    linarith
  intro h
  have h1 := (h (1/2) (by norm_num) (by norm_num)).1
  linarith
