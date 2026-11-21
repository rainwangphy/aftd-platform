import AFTD.Prelude

/-!
# boundary_clique_same_x_shore_count

Topic: graphs   Node: 8719975eb956

Provenance: helper lemma. OP-1957: arithmetic in the clique-block essential-edge classification; experiment 37117.

The displayed odd-shore, size and defect constraints force the three stated counts in the same-x placement.
-/

theorem boundary_clique_same_x_shore_count
    (k a b c d : ℕ) (hk : 5 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hd : d ≤ 2*k-5) (htotal : a+b+c+d=2*k)
    (hc3 : c ≤ 3) (hcodd : Odd c) (hy : a+b ≤ 3)
    (hotherC : 2 ≤ c → a+b ≤ 2)
    (hotherA : 2 ≤ a → c ≤ 2) :
    a=1 ∧ b=1 ∧ c=3 := by
  obtain ⟨i, hi⟩ := hcodd
  have hcne1 : c ≠ 1 := by omega
  have hc_eq : c=3 := by omega
  have hab : a+b=2 := by
    have h := hotherC (by omega)
    omega
  have ha1 : a=1 := by
    by_contra h
    have hh := hotherA (by omega)
    omega
  omega
