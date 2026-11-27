import AFTD.Prelude

/-!
# saturated_small_shore_three_c_vertices_pool_card_eq

Topic: graphs   Node: c65bec81aed4

Provenance: helper lemma. OP-1957: arithmetic reduction of the saturated positive-barrier branches.

In the first small-shore arithmetic branch, the displayed degree, separator, criticality and count inequalities force the pool vertex count eb to equal its group count m.
-/

theorem saturated_small_shore_three_c_vertices_pool_card_eq (k c m eb b0 b1 c0 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (hroot : b0+c0+eb+4=c)
    (htotal : b0+b1+eb+c0+d+m+4=2*k)
    (hb : b0+b1+eb+5≤2*k)
    (hrep0 : 1≤c0 → b1+eb+6≤c)
    (hcut : 1≤d → d+b1+eb+c≤2*k)
    (hcrit : (b0+b1+eb+5<2*k → m+b0+b1+eb+6≤2*k) ∧
      (b0+b1+eb+5=2*k → m≤1 ∧
        (if 1≤b0 then 1 else 0) + (if 1≤b1 then 1 else 0) + m ≤ 1)) :
    eb=m := by
  have hd : 1 ≤ d := by
    by_contra h
    have hz : d = 0 := by omega
    have hc0 : c0 = 0 := by
      by_contra hh
      have hrep := hrep0 (by omega)
      omega
    by_cases hlt : b0+b1+eb+5 < 2*k
    · have hh := hcrit.1 hlt
      omega
    · have heq : b0+b1+eb+5=2*k := by omega
      obtain ⟨hm,hs⟩ := hcrit.2 heq
      split_ifs at hs <;> omega
  have hh := hcut hd
  omega
