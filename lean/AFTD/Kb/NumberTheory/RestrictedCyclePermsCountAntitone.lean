import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount

/-!
# restricted_cycle_perms_count_antitone

Topic: elementary_number_theory   Node: 10ed7a1cc87a

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

Adding excluded cycle lengths can only decrease the number of qualifying permutations.
-/

theorem restricted_cycle_perms_count_antitone (n : ℕ) (S T : Finset ℕ) (h : S ⊆ T) :
    restricted_cycle_perms_count n T ≤ restricted_cycle_perms_count n S := by
  unfold restricted_cycle_perms_count
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro x hx
  exact hσ x (h hx)
