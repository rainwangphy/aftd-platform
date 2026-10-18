import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced

/-!
# finset_midpoint_balanced_card_ge_three

Topic: combinatorics   Node: 1bf0a1371101

Provenance: helper lemma. step towards finset_midpoint_balanced_exists_nonzero_minor

Every midpoint-balanced finite subset of an additive commutative monoid has cardinality at least 3.
-/

/-- Every midpoint-balanced finite subset of an additive commutative monoid has cardinality at least 3. -/
theorem finset_midpoint_balanced_card_ge_three {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (B : Finset G) (hB : finset_is_midpoint_balanced B) : 3 ≤ B.card := by
  rcases hB with ⟨⟨b, hb⟩, h⟩
  rcases h b hb with ⟨u, hu, v, hv, hub, hvb, huv, -⟩
  have hsub : {b, u, v} ⊆ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hb
    · exact hu
    · exact hv
  have hcard : ({b, u, v} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · simp [huv]
    · simp [hub.symm, hvb.symm]
  rw [← hcard]
  exact Finset.card_le_card hsub
