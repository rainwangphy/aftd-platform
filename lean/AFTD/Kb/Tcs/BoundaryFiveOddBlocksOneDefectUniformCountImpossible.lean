import AFTD.Prelude

/-!
# boundary_five_odd_blocks_one_defect_uniform_count_impossible

Topic: graphs   Node: de6fbe57a248

Provenance: helper lemma. OP-1957: compression of the five-by-odd-block one-defect barrier counts.

The listed natural-number endpoint, degree, separator and conditional odd-group-count inequalities cannot all hold, uniformly in the barrier size and the second block size.
-/

set_option maxHeartbeats 2000000

theorem boundary_five_odd_blocks_one_defect_uniform_count_impossible
    (k c s a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 : ℕ)
    (hkc : c ≤ k)
    (hR : s ≤ a2+b2+c2+d2)
    (ha0lo : 1 ≤ a0) (ha0hi : a0 ≤ 2) (hc1 : 1 ≤ c1)
    (hcsmall : c1+c2 ≤ 2)
    (htotal : a0+b0+c0+d0+a1+b1+c1+d1+a2+b2+c2+d2+s = 2*k)
    (hx : a1+c1+d1+a2+c2+d2 ≤ 3)
    (hy : a0+b0+c0+a2+b2+c2+2 ≤ c)
    (hqa0 : 2 ≤ a0 → a1+c1+d1+a2+c2+d2 ≤ 2)
    (hqc0 : 1 ≤ c0 → a1+b1+c1+a2+b2+c2+3 ≤ c)
    (hqd0 : 1 ≤ d0 → a1+b1+d1+a2+b2+d2+c+3 ≤ 2*k)
    (hcutd0 : 1 ≤ d0 → d0+b1+d1+b2+d2+c ≤ 2*k)
    (hqa1 : 1 ≤ a1 → a0+c0+d0+a2+c2+d2 ≤ 2)
    (hqc1 : 2 ≤ c1 → a0+b0+c0+a2+b2+c2+3 ≤ c)
    (hcutd1 : 1 ≤ d1 → d1+b0+d0+b2+d2+c ≤ 2*k)
    (hqa2 : 1 ≤ a2 → a0+c0+d0+a1+c1+d1 ≤ 2)
    (hqc2 : 1 ≤ c2 → a0+b0+c0+a1+b1+c1+s+2 ≤ c+d2)
    (hqd2 : 1 ≤ d2 → a0+b0+d0+a1+b1+d1+s+c+2 ≤ 2*k+c2)
    (hcrit : 1 ≤ b1 → s+(if b0%2=1 then 1 else 0)+b0+b1+b2+5 ≤ 2*k+a2+c2+d2)
    (hcritgroup : 1 ≤ b1 → 1 ≤ a2 → a0+c0+d0+a1+c1+d1 = 2 →
      s+(if (a2+c2+d2)%2=0 then 1 else 0)+(if b0%2=1 then 1 else 0)+b0+b1+b2+4 ≤ 2*k) : False := by
  split_ifs at * <;> omega
