import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsTwoRegular

/-!
# is_two_regular_of_submodule_stable

Topic: elementary_number_theory   Node: 2deecbcf7d39

Provenance: helper lemma. step towards halving_partition_sequence_two_regular

A sequence f : ℕ → ℤ is 2-regular if there exists a finitely generated ℤ-submodule N of ℤ^ℕ containing f that is closed under both decimation operations g ↦ (n ↦ g(2n)) and g ↦ (n ↦ g(2n+1)).
-/

/-- An integer sequence f is 2-regular if there exists a finitely generated ℤ-submodule containing f that is closed under both decimation operations g ↦ (n ↦ g(2n)) and g ↦ (n ↦ g(2n+1)). -/
theorem is_two_regular_of_submodule_stable (f : ℕ → ℤ)
    (N : Submodule ℤ (ℕ → ℤ)) (hN : N.FG) (hf : f ∈ N)
    (h0 : ∀ g ∈ N, (fun n => g (2 * n)) ∈ N)
    (h1 : ∀ g ∈ N, (fun n => g (2 * n + 1)) ∈ N) :
    is_two_regular f := by
  dsimp [is_two_regular]
  have h_dec : ∀ (e : ℕ) (r : ℕ), r < 2 ^ e → (fun n => f (2 ^ e * n + r)) ∈ N := by
    intro e
    induction' e with e ih
    · intro r hr
      have : r = 0 := by omega
      subst this
      have : (fun n => f (2 ^ 0 * n + 0)) = f := by
        funext n; simp
      rw [this]
      exact hf
    · intro r hr
      by_cases hr_lt : r < 2 ^ e
      · have h_step := h0 (fun n => f (2 ^ e * n + r)) (ih r hr_lt)
        have heq : (fun n => (fun m => f (2 ^ e * m + r)) (2 * n)) = (fun n => f (2 ^ (e + 1) * n + r)) := by
          funext n
          dsimp
          congr 1
          rw [pow_succ]
          ring
        rwa [heq] at h_step
      · have hr_le : 2 ^ e ≤ r := by omega
        have hr' : r - 2 ^ e < 2 ^ e := by
          rw [pow_succ] at hr
          omega
        have h_step := h1 (fun n => f (2 ^ e * n + (r - 2 ^ e))) (ih (r - 2 ^ e) hr')
        have heq : (fun n => (fun m => f (2 ^ e * m + (r - 2 ^ e))) (2 * n + 1)) = (fun n => f (2 ^ (e + 1) * n + r)) := by
          funext n
          dsimp
          congr 1
          rw [pow_succ]
          have h1 : 2 ^ e * (2 * n + 1) = 2 ^ e * 2 * n + 2 ^ e := by ring
          rw [h1, Nat.add_assoc, Nat.add_sub_cancel' hr_le]
        rwa [heq] at h_step
  apply hN.of_le
  rw [Submodule.span_le]
  rintro g ⟨e, r, hr, rfl⟩
  exact h_dec e r hr
