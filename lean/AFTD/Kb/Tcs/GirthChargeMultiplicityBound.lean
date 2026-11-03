import AFTD.Prelude

/-!
# girth_charge_multiplicity_bound

Topic: combinatorics   Node: 2aaa2b6e8416

Provenance: helper lemma. Girth-dependent collision accounting for the four-cycle campaign; experiment 13463.

A charged subset of an m-element parent set obeys the girth-dependent multiplicity bound if it is proper whenever the parent set has fewer than g elements.
-/

theorem girth_charge_multiplicity_bound (g m c : ℕ)
    (hg : 3 ≤ g) (hm : 2 ≤ m) (hc : c ≤ m)
    (hshort : m < g → c < m) : (g - 1) * c ≤ g * (m - 1) := by
  by_cases h : m < g
  · have hc' : c ≤ m - 1 := by have := hshort h; omega
    have h1 := Nat.mul_le_mul_left (g - 1) hc'
    have h2 : (g - 1) * (m - 1) ≤ g * (m - 1) :=
      Nat.mul_le_mul_right (m - 1) (by omega)
    exact h1.trans h2
  · have hgm : g ≤ m := by omega
    have h1 := Nat.mul_le_mul_left (g - 1) hc
    have h2 : (g - 1) * m ≤ g * (m - 1) := by
      calc
        (g - 1) * m = (g - 1) * ((m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = (g - 1) * (m - 1) + (g - 1) := by simp [Nat.mul_add]
        _ ≤ (g - 1) * (m - 1) + (m - 1) := Nat.add_le_add_left (Nat.sub_le_sub_right hgm 1) _
        _ = ((g - 1) + 1) * (m - 1) := by simp [Nat.add_mul]
        _ = g * (m - 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ g)]
    exact h1.trans h2
