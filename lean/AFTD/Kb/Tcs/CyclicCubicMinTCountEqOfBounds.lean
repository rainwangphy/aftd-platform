import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicMinTCount
import AFTD.Kb.Tcs.CyclicCubicSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# cyclic_cubic_min_t_count_eq_of_bounds

Topic: quantum   Node: 4a570e1fafa7

Provenance: helper lemma. step towards cyclic_cubic_phase_min_t_count_eq_two_n_add_five

If there exists a parity representation of cardinality k, and all parity representations have cardinality at least k, then cyclic_cubic_min_t_count n = k.
-/

/-- If there exists a parity representation of cardinality k, and all parity representations have cardinality at least k, then cyclic_cubic_min_t_count n = k. -/
theorem cyclic_cubic_min_t_count_eq_of_bounds (n k : ℕ) (h_ex : ∃ S : Finset (Finset (Fin n)), is_parity_repr S (cyclic_cubic_syndrome n) ∧ S.card = k) (h_lb : ∀ S : Finset (Finset (Fin n)), is_parity_repr S (cyclic_cubic_syndrome n) → k ≤ S.card) : cyclic_cubic_min_t_count n = k := by
  unfold cyclic_cubic_min_t_count
  apply le_antisymm
  · obtain ⟨S, hS, rfl⟩ := h_ex
    exact csInf_le (OrderBot.bddBelow _) ⟨S, hS, rfl⟩
  · apply le_csInf
    · obtain ⟨S, hS, rfl⟩ := h_ex
      exact ⟨S.card, S, hS, rfl⟩
    · rintro _ ⟨S, hS, rfl⟩
      exact h_lb S hS
