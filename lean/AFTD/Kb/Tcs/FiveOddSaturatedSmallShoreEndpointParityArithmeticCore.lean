import AFTD.Prelude

/-!
# five_odd_saturated_small_shore_endpoint_parity_arithmetic_core

Topic: graphs   Node: 2fa127fe5e13

Provenance: helper lemma. OP-1957, small shore aggregate transfer

The displayed endpoint-parity, degree, separator and factor-critical count constraints force one of two small-shore patterns. Parity of the exceptional groups is not assumed.
-/

set_option maxHeartbeats 2000000

theorem five_odd_saturated_small_shore_endpoint_parity_arithmetic_core
    (k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (ha : 1 ≤ a ∧ a ≤ 2) (hc1 : 1 ≤ c1)
    (he2 : (c2 = 0 ∧ b2 = 0) ∨ 1 ≤ c2)
    (he3 : (c3 = 0 ∧ b3 = 0) ∨ 1 ≤ c3)
    (hodd0 : Odd (a+b0+c0+d)) (hodd1 : Odd (b1+c1))
    (hs : m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + 1 ≤ c)
    (hb : b0+b1+b2+b3+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+b2+b3+eb+c0+c1+c2+c3+d+m+
      (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) = 2*k)
    (hsmall : c1+c2+c3 ≤ 3)
    (hrooty : a+b0+c0+b2+c2+b3+c3+eb+2 ≤ c)
    (hrepA : 2 ≤ a → c1+c2+c3 ≤ 2)
    (hrep0C : 1 ≤ c0 → b1+b2+b3+eb+c1+c2+c3+3 ≤ c)
    (hcutD : 1 ≤ d → d+b1+b2+b3+eb+c ≤ 2*k)
    (hrep1C : 2 ≤ c1 → a+b0+b2+b3+eb+c0+c2+c3+3 ≤ c)
    (hrep2C : 1 ≤ c2 → a+b0+b1+b3+eb+c0+c1+c3+3 ≤ c)
    (hrep3C : 1 ≤ c3 → a+b0+b1+b2+eb+c0+c1+c2+3 ≤ c)
    (hcrit : (b0+b1+b2+b3+eb+5 < 2*k →
        m+b0+b1+b2+b3+eb+6 ≤ 2*k) ∧
      (b0+b1+b2+b3+eb+5 = 2*k → m ≤ 1 ∧
        (if 1 ≤ b0 then 1 else 0) + (if 1 ≤ b1 then 1 else 0) +
        (if 1 ≤ b2 then 1 else 0) + (if 1 ≤ b3 then 1 else 0) + m ≤ 1))
    (hxconn : a=1 → c0+d=0 → b0=0) :
    a=1 ∧ ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
      (c1=1 ∧ c2+c3=2 ∧ (1 ≤ c2 → c2=1 ∧ b2+c2=1) ∧
        (1 ≤ c3 → c3=1 ∧ b3+c3=1))) := by
  have hcritical : (m+b0+b1+b2+b3+eb+6 ≤ 2*k) ∨
      (b0+b1+b2+b3+eb+5 = 2*k ∧ m ≤ 1 ∧
        (if 1 ≤ b0 then 1 else 0) + (if 1 ≤ b1 then 1 else 0) +
        (if 1 ≤ b2 then 1 else 0) + (if 1 ≤ b3 then 1 else 0) + m ≤ 1) := by
    by_cases h : b0+b1+b2+b3+eb+5 < 2*k
    · exact Or.inl (hcrit.1 h)
    · have heq : b0+b1+b2+b3+eb+5 = 2*k := by omega
      exact Or.inr ⟨heq, hcrit.2 heq⟩
  clear hcrit
  rcases hcritical with hpos | hfull
  all_goals rcases he2 with h2 | h2 <;> rcases he3 with h3 | h3
  all_goals obtain ⟨t0, ht0⟩ := hodd0
  all_goals obtain ⟨t1, ht1⟩ := hodd1
  all_goals simp_all
  all_goals first | omega | (split_ifs at * <;> omega)
