import AFTD.Prelude

/-!
# op1957_large_shore_nonempty_B_pool_contradiction

Topic: graphs   Node: 9927d3347e73

Provenance: helper lemma. OP-1957 positive-barrier large-shore counting reduction

For a positive B-only pool in the A-rich large-shore case, the displayed total, root-degree, representative-degree, separator and factor-criticality counts are inconsistent; no parity or B-representative inequality is required.
-/

theorem op1957_large_shore_nonempty_B_pool_contradiction
    (k c m eb a b0 b1 c0 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb) (hm : 1 ≤ m)
    (ha : 3 ≤ a ∧ a ≤ 4)
    (hb : b0+b1+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+eb+c0+1+d+m = 2*k)
    (hrooty : a+b0+c0+eb+2 ≤ c)
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
  have hb1 : 1 ≤ b1 := by omega
  have hconn := (hcrit.2 heq).2
  rw [if_pos hb1] at hconn
  omega
