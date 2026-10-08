import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.CondorcetWinningSetUniv

/-!
# condorcet_dimension_le_two_of_le_three

Topic: social_choice   Node: 0b52237f7b5c

Provenance: original. Related work: folklore

Every election with at most three candidates and at least one voter has a Condorcet winning set of at most two candidates.
-/

/-- Every election with at most three candidates and at least one voter has a Condorcet winning set of at most two candidates. -/
theorem condorcet_dimension_le_two_of_le_three (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hn : 0 < n) (hm : m ≤ 3) :
    ∃ S : Finset (Fin m), S.card ≤ 2 ∧ is_condorcet_winning_set P S := by
  classical
  rcases Nat.lt_or_ge m 3 with hm2 | hm3
  · exact ⟨Finset.univ, by simp; omega, condorcet_winning_set_univ P⟩
  obtain rfl : m = 3 := by omega
  let top : Fin 3 → Finset (Fin n) := fun a =>
    Finset.univ.filter fun v => ∀ b ∈ Finset.univ.erase a, P v a < P v b
  have hdisj : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint top := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro v hva hvb
    simp only [top, Finset.mem_filter] at hva hvb
    have h1 := hva.2 b (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ _⟩)
    have h2 := hvb.2 a (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩)
    exact absurd (h1.trans h2) (lt_irrefl _)
  have hsum : ∑ a, (top a).card ≤ n := by
    rw [← Finset.card_biUnion hdisj]
    exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨a, ha⟩ : ∃ a, 2 * (top a).card < n := by
    by_contra h
    push Not at h
    have h3 : ∑ _a : Fin 3, n ≤ ∑ a, 2 * (top a).card := Finset.sum_le_sum fun a _ => h a
    rw [← Finset.mul_sum] at h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    omega
  refine ⟨Finset.univ.erase a, by simp, fun x hx => ?_⟩
  have : x = a := by simpa using hx
  subst this
  exact ha
