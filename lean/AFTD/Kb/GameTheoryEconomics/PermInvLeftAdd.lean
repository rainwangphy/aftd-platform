import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PermCardValLt

/-!
# perm_inv_left_add

Topic: matching_markets   Node: 38b80371f011

For a permutation s of {0, ..., n-1} and a position g, the number of x < g with s(x) > s(g), plus s(g), equals the number of x > g with s(x) < s(g), plus g.
-/

theorem perm_inv_left_add {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Fin n) :
    (Finset.univ.filter fun x : Fin n => (x : ℕ) < g ∧ (σ g : ℕ) < σ x).card + (σ g : ℕ) =
      (Finset.univ.filter fun x : Fin n => (g : ℕ) < x ∧ (σ x : ℕ) < σ g).card + (g : ℕ) := by
  have hA := perm_card_val_lt σ (σ g)
  have key : (Finset.univ.filter fun x : Fin n => (x : ℕ) < g ∧ (σ g : ℕ) < σ x).card +
      (Finset.univ.filter fun x : Fin n => (σ x : ℕ) < σ g).card =
      (Finset.univ.filter fun x : Fin n => (g : ℕ) < x ∧ (σ x : ℕ) < σ g).card +
      (Finset.univ.filter fun x : Fin n => (x : ℕ) < g).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : (x : ℕ) = g → (σ x : ℕ) = σ g := fun h => by rw [Fin.val_inj.mp h]
    have h2 : (σ x : ℕ) = σ g → (x : ℕ) = g := fun h => by
      rw [σ.injective (Fin.val_inj.mp h)]
    split_ifs <;> omega
  have hB : (Finset.univ.filter fun x : Fin n => (x : ℕ) < g).card = g := by
    have := perm_card_val_lt (Equiv.refl (Fin n)) g
    simpa using this
  rw [hA, hB] at key
  exact key
