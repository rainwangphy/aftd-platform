import AFTD.Prelude

/-!
# trianglefree_parent_charge_weight_bound

Topic: combinatorics   Node: 4f2ff04fe110

Provenance: helper lemma. Triangle-free center budget for the four-cycle campaign; experiment 13471.

If a charged subset of m parents is proper whenever m is less than four, then three times parents plus charges is bounded by eight times overlap plus one exactly when m is two.
-/

theorem trianglefree_parent_charge_weight_bound (m c : ℕ)
    (hm : 2 ≤ m) (hc : c ≤ m) (hshort : m < 4 → c < m) :
    3 * (m + c) ≤ 8 * (m - 1) + (if m = 2 then 1 else 0) := by
  by_cases h2 : m = 2
  · subst m
    have h := hshort (by decide)
    simp
    omega
  · by_cases h3 : m = 3
    · subst m
      have h := hshort (by decide)
      simp
      omega
    · simp [h2]
      omega
