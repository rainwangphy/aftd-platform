import AFTD.Prelude

/-!
# complement_adjacent_twins_have_equal_open_neighbors

Topic: graphs   Node: 73142de98a53

Provenance: helper lemma. OP-1957 uniform bridge-family endpoint bound.

Adjacent complement twins are nonadjacent false twins in the original graph.
-/

theorem complement_adjacent_twins_have_equal_open_neighbors
    {V : Type*} (H : SimpleGraph V) (x y : V) (hxy : H.Adj x y)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a)) :
    (Hᶜ).neighborSet x = (Hᶜ).neighborSet y := by
  classical
  ext a
  change (Hᶜ).Adj x a ↔ (Hᶜ).Adj y a
  by_cases hax : a = x
  · subst a
    simp [hxy.symm]
  · by_cases hay : a = y
    · subst a
      simp [hxy]
    · simp only [SimpleGraph.compl_adj]
      have hxa : x ≠ a := fun h => hax h.symm
      have hya : y ≠ a := fun h => hay h.symm
      simp [hxa,hya,htwin a hax hay]
