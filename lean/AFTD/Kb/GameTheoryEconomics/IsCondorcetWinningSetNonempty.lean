import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# is_condorcet_winning_set_nonempty

Topic: social_choice   Node: a221111f4221

Provenance: original. Related work: folklore

In an election with at least one voter and at least one candidate, every Condorcet winning set is nonempty.
-/

/-- Every Condorcet winning set is nonempty in an election with at least one voter and at least one candidate. -/
theorem is_condorcet_winning_set_nonempty {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (P : Fin n → Equiv.Perm (Fin m)) {S : Finset (Fin m)}
    (hS : is_condorcet_winning_set P S) : S.Nonempty := by
  by_contra h_empty
  rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
  have ha : (⟨0, hm⟩ : Fin m) ∉ S := by simp [h_empty]
  have h_cond := hS ⟨0, hm⟩ ha
  rw [h_empty] at h_cond
  have h_all : ({v | ∀ b ∈ (∅ : Finset (Fin m)), (P v) ⟨0, hm⟩ < (P v) b} : Finset (Fin n)) = Finset.univ := by
    ext v
    simp
  rw [h_all] at h_cond
  simp only [Finset.card_univ, Fintype.card_fin] at h_cond
  omega
