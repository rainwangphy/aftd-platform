import AFTD.Prelude
import AFTD.Kb.Tcs.SizePriorityMatchingCardLe
import AFTD.Kb.Tcs.SizePriorityMatching

/-!
# size_priority_matching_symmDiff_card_le

Topic: graphs   Node: e128979defb3

Provenance: helper lemma. arXiv:2601.20502, Optimal matching under size priority

For every n, every edge set E ⊆ Fin n × Fin n, and all real cost functions w₁ and w₂, the symmetric difference of the size-priority optimal matchings size_priority_matching n E w₁ and size_priority_matching n E w₂ has cardinality at most 2 * n.
-/

/-- The symmetric difference of any two size-priority optimal matchings on Fin n + Fin n has cardinality at most 2n. -/
theorem size_priority_matching_symmDiff_card_le (n : ℕ) (E : Finset (Fin n × Fin n))
    (w₁ w₂ : Fin n × Fin n → ℝ) :
    (symmDiff (size_priority_matching n E w₁) (size_priority_matching n E w₂)).card ≤ 2 * n := by
  have h1 : (size_priority_matching n E w₁).card ≤ n := size_priority_matching_card_le n E w₁
  have h2 : (size_priority_matching n E w₂).card ≤ n := size_priority_matching_card_le n E w₂
  have h := (show (symmDiff (size_priority_matching n E w₁) (size_priority_matching n E w₂)).card
      ≤ (size_priority_matching n E w₁).card + (size_priority_matching n E w₂).card from by
    calc (symmDiff (size_priority_matching n E w₁) (size_priority_matching n E w₂)).card
        ≤ (size_priority_matching n E w₁ ∪ size_priority_matching n E w₂).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_symmDiff] at hx
          simp only [Finset.mem_union]
          exact hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    _ ≤ _ := Finset.card_union_le _ _)
  omega
