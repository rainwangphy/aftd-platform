import AFTD.Prelude

/-!
# boundary_clique_same_y_shore_count

Topic: graphs   Node: c4b0134c1231

Provenance: helper lemma. OP-1957: arithmetic in the clique-block essential-edge classification; experiment 37117.

The displayed odd-shore, size and defect constraints force the three stated counts in the same-y placement.
-/

theorem boundary_clique_same_y_shore_count
    (k a b c d : ℕ) (hk : 5 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hb : b ≤ 2*k-5) (htotal : a+b+c+d=2*k)
    (ha3 : a ≤ 3) (haodd : Odd a) (hx : c+d ≤ 3)
    (hotherA : 2 ≤ a → c+d ≤ 2)
    (hotherC : 2 ≤ c → a ≤ 2) :
    a=3 ∧ c=1 ∧ d=1 := by
  obtain ⟨i, hi⟩ := haodd
  have hane1 : a ≠ 1 := by omega
  have ha_eq : a=3 := by omega
  have hcd : c+d=2 := by
    have h := hotherA (by omega)
    omega
  have hc1 : c=1 := by
    by_contra h
    have hh := hotherC (by omega)
    omega
  omega
