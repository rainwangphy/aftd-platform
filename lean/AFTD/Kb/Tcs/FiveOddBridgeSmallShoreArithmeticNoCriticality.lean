import AFTD.Prelude

/-!
# five_odd_bridge_small_shore_arithmetic_no_criticality

Topic: graphs   Node: b1361667a771

Provenance: helper lemma. OP-1957; forced-edge saturated barrier reduction.

For the displayed zero-separator small-shore scalar inequalities with no exceptional groups, the small-shore defect count follows without a B-block criticality inequality.
-/

theorem five_odd_bridge_small_shore_arithmetic_no_criticality
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
    (hm : m=0) (heb0 : eb=0) (hb2 : b2=0) (hb3 : b3=0)
    (hc2 : c2=0) (hc3 : c3=0)
    :
    a=1 ∧ ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
      (c1=1 ∧ c2+c3=2 ∧ (1 ≤ c2 → c2=1 ∧ b2+c2=1) ∧
        (1 ≤ c3 → c3=1 ∧ b3+c3=1))) := by
  subst m
  subst eb
  subst b2
  subst b3
  subst c2
  subst c3
  obtain ⟨t0,ht0⟩ := hodd0
  obtain ⟨t1,ht1⟩ := hodd1
  simp_all
  all_goals omega
