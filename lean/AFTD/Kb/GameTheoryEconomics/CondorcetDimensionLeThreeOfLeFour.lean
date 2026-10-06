import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.CondorcetWinningSetUniv

/-!
# condorcet_dimension_le_three_of_le_four

Topic: social_choice   Node: 9c353d216d76

Provenance: original. Related work: smallest nontrivial case of the question whether the Condorcet dimension is always at most 3 (Condorcet winning sets (Social Choice and Welfare 44(3):493-517, 2015); arXiv:2604.19851 states the gap 3 ≤ dim ≤ 5 as open)

Every election with at most four candidates (and at least one voter) has a Condorcet winning set of at most three candidates: drop a candidate ranked first by fewer than half of the voters.
-/

theorem condorcet_dimension_le_three_of_le_four (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hn : 0 < n) (hm : m ≤ 4) :
    ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S := by
  classical
  rcases Nat.lt_or_ge m 4 with hm3 | hm4
  · exact ⟨Finset.univ, by simp; omega, condorcet_winning_set_univ P⟩
  obtain rfl : m = 4 := by omega
  let top : Fin 4 → Finset (Fin n) := fun a =>
    Finset.univ.filter fun v => ∀ b ∈ Finset.univ.erase a, P v a < P v b
  have hdisj : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint top := by
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
    have h4 : ∑ _a : Fin 4, n ≤ ∑ a, 2 * (top a).card := Finset.sum_le_sum fun a _ => h a
    rw [← Finset.mul_sum] at h4
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  refine ⟨Finset.univ.erase a, by simp, fun x hx => ?_⟩
  have : x = a := by simpa using hx
  subst this
  exact ha
