import AFTD.Prelude

/-!
# saturated_small_shore_pool_card_eq_groups

Topic: graphs   Node: 0b59adf18c46

Provenance: helper lemma. OP-1957; small-shore aggregate strengthening suggested by experiments 40052, 40053 and 40055.

Under the displayed small-shore pattern and count inequalities, the B-only pool cardinality equals its number of odd groups and the first shore contains at least two D vertices; the exceptional pattern has an empty B intersection on the y shore, at least six D vertices, and m+6≤c.
-/

theorem saturated_small_shore_pool_card_eq_groups
    (k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (hpat : a=1 ∧ ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
      (c1=1 ∧ c2+c3=2 ∧ (1 ≤ c2 → c2=1 ∧ b2+c2=1) ∧
        (1 ≤ c3 → c3=1 ∧ b3+c3=1))))
    (he2 : (c2=0 ∧ b2=0) ∨ 1 ≤ c2)
    (he3 : (c3=0 ∧ b3=0) ∨ 1 ≤ c3)
    (hodd0 : Odd (a+b0+c0+d))
    (hs : m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + 1 ≤ c)
    (hb : b0+b1+b2+b3+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+b2+b3+eb+c0+c1+c2+c3+d+m+
      (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) = 2*k)
    (hrep0C : 1 ≤ c0 → b1+b2+b3+eb+c1+c2+c3+3 ≤ c)
    (hcutD : 1 ≤ d → d+b1+b2+b3+eb+c ≤ 2*k)
    (hrep2C : 1 ≤ c2 → a+b0+b1+b3+eb+c0+c1+c3+3 ≤ c)
    (hcrit : (b0+b1+b2+b3+eb+5 < 2*k →
        m+b0+b1+b2+b3+eb+6 ≤ 2*k) ∧
      (b0+b1+b2+b3+eb+5 = 2*k → m ≤ 1 ∧
        (if 1 ≤ b0 then 1 else 0) + (if 1 ≤ b1 then 1 else 0) +
        (if 1 ≤ b2 then 1 else 0) + (if 1 ≤ b3 then 1 else 0) + m ≤ 1)) :
    eb=m ∧ 2 ≤ d ∧ (c1=1 → b1=0 ∧ m+6 ≤ c ∧ 6 ≤ d) := by
  obtain ⟨t,ht⟩ := hodd0
  rcases hpat with ⟨ha,hpat | hpat⟩ <;> rcases he2 with h2 | h2 <;> rcases he3 with h3 | h3
  all_goals simp_all
  all_goals first | omega | (split_ifs at * <;> omega)
