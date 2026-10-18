import AFTD.Prelude

/-!
# mdfrbf_fibre_subset

Topic: combinatorics   Node: 6d3024b35998

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Pigeonhole: if f : Fin d → Fin b and b*n < d, then some fibre of f contains n+1 points; equivalently there are a colour c and a set W of n+1 points on which f is constantly c.
-/

/-- Pigeonhole step extracting j-1 = n+1 points sharing one fan colour. -/
theorem mdfrbf_fibre_subset {d b : ℕ} (f : Fin d → Fin b) (n : ℕ) (h : b * n < d) :
    ∃ c : Fin b, ∃ W : Finset (Fin d), W.card = n + 1 ∧ ∀ w ∈ W, f w = c := by
  classical
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := n) (by simpa using h)
  refine ⟨c, ?_⟩
  have hc' : n + 1 ≤ (Finset.univ.filter (fun x => f x = c)).card := hc
  obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq hc'
  exact ⟨W, hWc, fun w hw => by simpa using hW hw⟩
