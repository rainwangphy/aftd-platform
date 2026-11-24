import AFTD.Prelude

/-!
# five_odd_saturated_large_shore_arithmetic_core

Topic: graphs   Node: 1c63b43f4b77

Provenance: helper lemma. OP-1957: small arithmetic core for the unbounded saturated large-shore count reduction.

The displayed natural-number endpoint, degree, separator and B-component inequalities cannot all hold in the A-rich aggregate obstruction.
-/

set_option maxHeartbeats 1000000

theorem five_odd_saturated_large_shore_arithmetic_core
    (k c m eb a b0 b1 c0 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (ha : 3 ≤ a ∧ a ≤ 4) (hodd : Odd (a+b0+c0+d))
    (hb : b0+b1+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+eb+c0+1+d+m = 2*k)
    (hrooty : a+b0+c0+eb+2 ≤ c)
    (hrepB : 1 ≤ b0 → b1+eb+9 ≤ 2*k)
    (hrepC : 1 ≤ c0 → b1+eb+4 ≤ c)
    (hcutD : 1 ≤ d → d+b1+eb+c ≤ 2*k)
    (hcrit : (b0+b1+eb+5 < 2*k → m+b0+b1+eb+6 ≤ 2*k) ∧
      (b0+b1+eb+5 = 2*k → m ≤ 1 ∧
        (if 1 ≤ b0 then 1 else 0) + (if 1 ≤ b1 then 1 else 0) + m ≤ 1)) : False := by
  have hd : d = 0 := by
    by_contra hn
    have h := hcutD (by omega)
    omega
  have hc0 : c0 = 0 := by
    by_contra hn
    have h := hrepC (by omega)
    omega
  have heq : b0+b1+eb+5 = 2*k := by
    by_contra hn
    have h := hcrit.1 (by omega)
    omega
  have hconnected := (hcrit.2 heq).2
  have hb1 : 1 ≤ b1 := by omega
  rw [if_pos hb1] at hconnected
  have hm : m = 0 := by omega
  have hb0 : b0 = 0 := by
    by_contra hn
    have hb0pos : 1 ≤ b0 := by omega
    rw [if_pos hb0pos] at hconnected
    omega
  have ha4 : a = 4 := by omega
  obtain ⟨t, ht⟩ := hodd
  omega
