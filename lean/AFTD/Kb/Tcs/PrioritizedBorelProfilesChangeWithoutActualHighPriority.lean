import AFTD.Prelude

/-!
# prioritized_borel_profiles_change_without_actual_high_priority

Topic: automata   Node: 0e2385a8702a

Provenance: helper lemma.

There are binary profiles that strictly increase at every depth while the actual priority sequence has its last high-priority event at time zero; the profiles are the all-high finite prefixes padded with low bits.
-/

theorem prioritized_borel_profiles_change_without_actual_high_priority :
    ∃ (actual : ℕ → Bool) (profiles : ℕ → ℕ → Bool),
      actual 0 = true ∧ (∀ n, actual (n+1) = false) ∧
      (∀ n i, profiles n i = decide (i < n)) ∧
      (∀ n, toLex (profiles n) < toLex (profiles (n+1))) := by
  classical
  refine ⟨fun i => decide (i = 0), fun n i => decide (i < n), by simp, ?_, ?_, ?_⟩
  · intro n
    simp
  · intro n i
    rfl
  · intro n
    change Pi.Lex (· < ·) (· < ·) (fun i => decide (i < n))
      (fun i => decide (i < n+1))
    refine ⟨n, ?_, ?_⟩
    · intro i hi
      have hi' : i < n+1 := by omega
      simp [hi, hi']
    · simp
