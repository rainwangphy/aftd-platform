import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# electrical_flow_cross_term

Topic: online_algorithms   Node: 4f54df3b9fa7

Provenance: helper lemma. arXiv:2611.05669, Appendix A

If F is a skew-symmetric flow on Fin k satisfying the voltage law d i j * F i j = h i - h j for all i ≠ j, and G is a skew-symmetric flow with divergence b (so ∑ j, G i j = b i for all i), then the cross term ∑ i, ∑ j with i < j, d i j * F i j * G i j equals ∑ i, b i * h i.
-/

/-- The cross term in the energy of a potential-induced flow and a feasible flow equals the inner product of potentials and demands. -/
theorem electrical_flow_cross_term {k : ℕ} (d : Fin k → Fin k → ℝ) (F G : Fin k → Fin k → ℝ) (h : Fin k → ℝ) (b : Fin k → ℝ) (hF_skew : ∀ i j, F i j = -F j i) (hF_volt : ∀ i j, i ≠ j → d i j * F i j = h i - h j) (hG_skew : ∀ i j, G i j = -G j i) (hG_div : ∀ i, ∑ j, G i j = b i) : (∑ i : Fin k, ∑ j with i < j, d i j * F i j * G i j) = ∑ i, b i * h i := by
  have _ := hF_skew
  have h1 : (∑ i : Fin k, ∑ j with i < j, d i j * F i j * G i j) =
      ∑ i, ∑ j, if i < j then (h i - h j) * G i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · rw [hF_volt i j (ne_of_lt hij)]
    · rfl
  rw [h1]
  have h2 : (∑ i : Fin k, ∑ j, if i < j then (h i - h j) * G i j else (0 : ℝ)) =
      (∑ i, ∑ j, if i < j then h i * G i j else 0) -
      (∑ i, ∑ j, if i < j then h j * G i j else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h2]
  have h3 : (∑ i : Fin k, ∑ j, if i < j then h j * G i j else (0 : ℝ)) =
      - ∑ i, ∑ j, if j < i then h i * G i j else 0 := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hG_skew j i]
    split_ifs <;> ring
  rw [h3, sub_neg_eq_add, ← Finset.sum_add_distrib]
  have h4 : ∀ i : Fin k, (∑ j, if i < j then h i * G i j else 0) +
      (∑ j, if j < i then h i * G i j else 0) = b i * h i := by
    intro i
    rw [← Finset.sum_add_distrib]
    have hterm : (∑ j, ((if i < j then h i * G i j else 0) + (if j < i then h i * G i j else 0))) =
        ∑ j, h i * G i j := by
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with hij | rfl | hji
      · rw [if_pos hij, if_neg (asymm hij), add_zero]
      · have hG0 : G i i = 0 := by have := hG_skew i i; linarith
        simp [hG0]
      · rw [if_pos hji, if_neg (asymm hji), zero_add]
    rw [hterm, ← Finset.mul_sum, hG_div i, mul_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact h4 i
