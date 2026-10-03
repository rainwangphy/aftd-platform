import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids

/-!
# procurement_others_bids_nonneg

Topic: mechanism_design   Node: 738c086451c8

If every agent bids nonnegatively, so do the others of any agent.
-/

lemma procurement_others_bids_nonneg {n : ℕ} (β : Fin n → List ℝ) (hβ : ∀ i, ∀ b ∈ β i, 0 ≤ b)
    (i : Fin n) : ∀ x ∈ procurement_others_bids β i, 0 ≤ x := by
  intro x hx
  unfold procurement_others_bids at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨j, _, hj⟩ := hx
  split_ifs at hj with h
  · simp at hj
  · exact hβ j x hj
