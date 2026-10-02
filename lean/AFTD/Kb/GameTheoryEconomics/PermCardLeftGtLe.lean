import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PermCardValLt

/-!
# perm_card_left_gt_le

Topic: matching_markets   Node: e161114dad6e

For a permutation s of {0, ..., n-1} and a position x with x <= s(x), the number of i < x with s(i) > s(x) is at most the number of j > x with s(j) < x.
-/

theorem perm_card_left_gt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n)
    (hx : (x : ℕ) ≤ σ x) :
    (Finset.univ.filter fun i : Fin n => (i : ℕ) < x ∧ (σ x : ℕ) < σ i).card ≤
      (Finset.univ.filter fun j : Fin n => (x : ℕ) < j ∧ (σ j : ℕ) < x).card := by
  have hA := perm_card_val_lt σ x
  have hB : (Finset.univ.filter fun i : Fin n => (i : ℕ) < x).card = x := by
    have := perm_card_val_lt (Equiv.refl (Fin n)) x
    simpa using this
  have key : (Finset.univ.filter fun i : Fin n => (i : ℕ) < x ∧ (x : ℕ) ≤ σ i).card +
      (Finset.univ.filter fun i : Fin n => (σ i : ℕ) < x).card =
      (Finset.univ.filter fun j : Fin n => (x : ℕ) ≤ j ∧ (σ j : ℕ) < x).card +
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < x).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  rw [hA, hB] at key
  have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < x ∧ (x : ℕ) ≤ σ i).card =
      (Finset.univ.filter fun j : Fin n => (x : ℕ) ≤ j ∧ (σ j : ℕ) < x).card := by omega
  calc (Finset.univ.filter fun i : Fin n => (i : ℕ) < x ∧ (σ x : ℕ) < σ i).card
      ≤ (Finset.univ.filter fun i : Fin n => (i : ℕ) < x ∧ (x : ℕ) ≤ σ i).card := by
        apply Finset.card_le_card
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        omega
    _ = (Finset.univ.filter fun j : Fin n => (x : ℕ) ≤ j ∧ (σ j : ℕ) < x).card := e
    _ ≤ (Finset.univ.filter fun j : Fin n => (x : ℕ) < j ∧ (σ j : ℕ) < x).card := by
        apply Finset.card_le_card
        intro j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        refine ⟨?_, h.2⟩
        rcases Nat.lt_or_eq_of_le h.1 with h' | h'
        · exact h'
        · exfalso
          have : j = x := Fin.val_inj.mp h'.symm
          subst this
          omega
