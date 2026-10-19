import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# card_filter_gt_card_filter_of_lt

Topic: graphs   Node: 698be0d3afec

Provenance: helper lemma. step towards op223_poset_connectivity

For f : α → β with β linearly ordered and α finite, if f a < f b then strictly fewer elements of α have f-value above f b than above f a.
-/

/-- The count of states with f-value above a threshold is strictly decreasing in the threshold. -/
theorem card_filter_gt_card_filter_of_lt {α β : Type*} [Fintype α] [LinearOrder β] (f : α → β)
    {a b : α} (hab : f a < f b) :
    (Finset.univ.filter (fun W : α => f b < f W)).card <
      (Finset.univ.filter (fun W : α => f a < f W)).card := by
  classical
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    exact lt_trans hab hW
  · intro hEq
    have hmem : b ∈ Finset.univ.filter (fun W : α => f a < f W) := by simp [hab]
    rw [← hEq] at hmem
    simp at hmem
