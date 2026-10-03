import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids

/-!
# procurement_others_bids_sum

Topic: mechanism_design   Node: 8468b8a65394

The total of the other agents' bids is the total of all bids minus agent i's total.
-/

lemma procurement_others_bids_sum {n : ℕ} (β : Fin n → List ℝ) (i : Fin n) :
    (procurement_others_bids β i).sum = (∑ j, (β j).sum) - (β i).sum := by
  unfold procurement_others_bids
  rw [List.flatMap_def, List.sum_flatten, List.map_map, ← Fin.sum_univ_def]
  have h : ∀ j, (List.sum ∘ fun j => if j = i then ([] : List ℝ) else β j) j =
      (β j).sum - if j = i then (β j).sum else 0 := by
    intro j; by_cases hj : j = i <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
  simp
