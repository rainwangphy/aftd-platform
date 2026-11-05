import AFTD.Prelude
import AFTD.Kb.Tcs.IsBalancedIndicator

/-!
# coordinate_indicator_is_balanced

Topic: information   Node: bbe46571cd8c

Provenance: helper lemma. arXiv:2611.00868, Section 1

For every positive integer n, coordinate i : Fin n, and boolean value b, the signed coordinate indicator x ↦ if x i = b then 1 else 0 is a balanced Boolean indicator.
-/

/-- Sanity lemma: signed coordinate indicators are balanced Boolean indicators. -/
lemma coordinate_indicator_is_balanced (n : ℕ) (hn : 0 < n) (i : Fin n) (b : Bool) :
    is_balanced_indicator n (fun x ↦ if x i = b then 1 else 0) := by
  dsimp [is_balanced_indicator]
  refine ⟨?_, ?_⟩
  · intro x
    split_ifs
    · right; rfl
    · left; rfl
  · have h_sum : (∑ x : Fin n → Bool, (if x i = b then (1 : ℝ) else 0)) = (2 : ℝ) ^ (n - 1) := by
      let e := Equiv.piSplitAt i (fun _ => Bool)
      have h_eq : ∀ x, (if x i = b then (1 : ℝ) else 0) =
          (fun p : Bool × ({ j // j ≠ i } → Bool) ↦ if p.1 = b then (1 : ℝ) else 0) (e x) := by
        intro x
        rfl
      rw [Fintype.sum_equiv e (fun x => if x i = b then (1 : ℝ) else 0)
        (fun p => if p.1 = b then (1 : ℝ) else 0) h_eq]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp
    rw [h_sum]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
    simp [pow_succ]
