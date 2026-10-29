import AFTD.Prelude

/-!
# exists_le_mul_of_le_sum

Topic: combinatorics   Node: f3a81670f2ab

Provenance: helper lemma. arXiv:2610.37315 Claim 1.2

Let α be a type, let F be a finite subset of α with cardinality k where 1 ≤ k, and let f : α → ℕ be a function. If S ≤ ∑ x ∈ F, f x, then there exists an element x ∈ F such that S ≤ k * f x.
-/

/-- Averaging lemma: if a sum of nonnegative integers over a set of size k ≥ 1 is at least S, then some term is at least S/k. -/
lemma exists_le_mul_of_le_sum {α : Type*} (F : Finset α) (f : α → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.card = k) (S : ℕ) (hsum : S ≤ ∑ x ∈ F, f x) :
    ∃ x ∈ F, S ≤ k * f x := by
  have hne : F.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hk
  have h_sum_le : ∑ x ∈ F, S ≤ ∑ x ∈ F, (k * f x) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
    exact Nat.mul_le_mul_left k hsum
  obtain ⟨x, hx, hle⟩ := Finset.exists_le_of_sum_le hne h_sum_le
  exact ⟨x, hx, hle⟩
