import AFTD.Prelude

/-!
# boundary_clique_opposite_shore_count_impossible

Topic: graphs   Node: c60d4126ae1e

Provenance: helper lemma. OP-1957: arithmetic in the clique-block essential-edge classification; experiment 37117.

The displayed small-block defect and separator counts are inconsistent.
-/

theorem boundary_clique_opposite_shore_count_impossible
    (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (ha3 : a ≤ 3) (hc3 : c ≤ 3)
    (hpair : 2 ≤ a → 2 ≤ c → a ≤ 2 ∧ c ≤ 2)
    (hsep : 5 ≤ a+c) : False := by
  by_cases ha2 : 2 ≤ a
  · by_cases hc2 : 2 ≤ c
    · obtain ⟨h1,h2⟩ := hpair ha2 hc2
      omega
    · omega
  · omega
