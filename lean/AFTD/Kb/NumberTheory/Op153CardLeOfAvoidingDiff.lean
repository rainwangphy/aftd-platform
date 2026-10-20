import AFTD.Prelude

/-!
# op_153_card_le_of_avoiding_diff

Topic: elementary_number_theory   Node: f6ffa281a142

Provenance: helper lemma. folklore

For every positive integer $k$, every subset $A \subseteq \{1, \dots, 2k\}$ such that no two distinct elements of $A$ have difference equal to $k$ satisfies $|A| \le k$.
-/

/-- Any subset of {1, ..., 2k} avoiding difference k has cardinality at most k. -/
theorem op_153_card_le_of_avoiding_diff (k : ℕ) (hk : 0 < k) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 (2 * k))
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a : ℤ) - b ≠ (k : ℤ)) :
    A.card ≤ k := by
  let f : ℕ → ℕ := fun x => if x ≤ k then x else x - k
  have hmaps : Set.MapsTo f (A : Set ℕ) (Finset.Icc 1 k : Set ℕ) := by
    intro x hx
    rw [Finset.mem_coe] at hx ⊢
    have hx' := hA hx
    rw [Finset.mem_Icc] at hx' ⊢
    dsimp [f]
    split_ifs <;> omega
  have hinj : (A : Set ℕ).InjOn f := by
    intro a ha b hb hfab
    rw [Finset.mem_coe] at ha hb
    dsimp [f] at hfab
    by_contra hne
    have hd1 := hdiff a ha b hb hne
    have hd2 := hdiff b hb a ha (Ne.symm hne)
    split_ifs at hfab <;> omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Nat.card_Icc] at hcard
  omega
