import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# card_filter_lt_card_filter_of_lt

Topic: graphs   Node: b6fd13c8392c

Provenance: helper lemma. step towards op223_poset_connectivity

For f : α → β with β linearly ordered and α finite, if f a < f b then strictly fewer elements of α have f-value below f a than below f b.
-/

/-- The count of states with f-value below a threshold is strictly increasing in the threshold. -/
theorem card_filter_lt_card_filter_of_lt {α β : Type*} [Fintype α] [LinearOrder β] (f : α → β)
    {a b : α} (hab : f a < f b) :
    (Finset.univ.filter (fun W : α => f W < f a)).card <
      (Finset.univ.filter (fun W : α => f W < f b)).card := by
  classical
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    exact lt_trans hW hab
  · intro hEq
    have hmem : a ∈ Finset.univ.filter (fun W : α => f W < f b) := by simp [hab]
    rw [← hEq] at hmem
    simp at hmem
