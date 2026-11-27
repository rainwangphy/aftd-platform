import AFTD.Prelude
import AFTD.Kb.Tcs.FiveOddSaturatedSmallShoreArithmeticNoConnectedness
import AFTD.Kb.Tcs.SaturatedSmallShoreThreeCVerticesPoolCardEq
import AFTD.Kb.Tcs.SaturatedSmallShoreTwoExceptionalSingletonsPoolCardEq

/-!
# saturated_positive_small_shore_forces_two_singleton_groups

Topic: graphs   Node: c3fbeb426f33

Provenance: helper lemma. OP-1957: positive-barrier reduction after the strict common-nonneighbor pool bound.

Under the displayed small-shore count conditions, a positive barrier, and the implication that a singleton pool has no groups, the B-only pool is empty, the second shore has no B vertices and has one C vertex, and each of the two exceptional groups has one C vertex.
-/

theorem saturated_positive_small_shore_forces_two_singleton_groups
    (k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (ha : 1 ≤ a ∧ a ≤ 2) (hc1 : 1 ≤ c1)
    (he2 : (c2 = 0 ∧ b2 = 0) ∨ 1 ≤ c2)
    (he3 : (c3 = 0 ∧ b3 = 0) ∨ 1 ≤ c3)
    (hodd0 : Odd (a+b0+c0+d)) (hodd1 : Odd (b1+c1))
    (hs : m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + 1 ≤ c)
    (hspos : 1 ≤ m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0))
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
    (hpool : eb=m → m=0) :
    m=0 ∧ eb=0 ∧ b1=0 ∧ c1=1 ∧ c2=1 ∧ c3=1 := by
  have hsplit := five_odd_saturated_small_shore_arithmetic_no_connectedness
    k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d hc hkc heb ha hc1 he2 he3 hodd0 hodd1 hs hb htotal hsmall
    hrooty hrepA hrep0C hcutD hrep1C hrep2C hrep3C hcrit
  rcases hsplit with ⟨ha1, ⟨hc1_3, hc23_0, hroot⟩ | ⟨hc1_1, hc23_2, hsingle2, hsingle3⟩⟩
  · have hc2 : c2 = 0 := by omega
    have hc3 : c3 = 0 := by omega
    have hb2 : b2 = 0 := by
      rcases he2 with ⟨_, hb2⟩ | h2
      · exact hb2
      · omega
    have hb3 : b3 = 0 := by
      rcases he3 with ⟨_, hb3⟩ | h3
      · exact hb3
      · omega
    have h1 : 1 ≤ m := by
      have : (if 1 ≤ c2 then 1 else 0) = 0 := by simp [hc2]
      have : (if 1 ≤ c3 then 1 else 0) = 0 := by simp [hc3]
      omega
    have hroot' : b0 + c0 + eb + 4 = c := by omega
    have htotal' : b0 + b1 + eb + c0 + d + m + 4 = 2 * k := by
      have : (if 1 ≤ c2 then 1 else 0) = 0 := by simp [hc2]
      have : (if 1 ≤ c3 then 1 else 0) = 0 := by simp [hc3]
      omega
    have hb' : b0 + b1 + eb + 5 ≤ 2 * k := by omega
    have hrep0' : 1 ≤ c0 → b1 + eb + 6 ≤ c := by
      intro hc0
      have := hrep0C hc0
      omega
    have hcut' : 1 ≤ d → d + b1 + eb + c ≤ 2 * k := by
      intro hd
      have := hcutD hd
      omega
    have hcrit' : (b0 + b1 + eb + 5 < 2 * k → m + b0 + b1 + eb + 6 ≤ 2 * k) ∧
      (b0 + b1 + eb + 5 = 2 * k → m ≤ 1 ∧
        ((if 1 ≤ b0 then 1 else 0) + (if 1 ≤ b1 then 1 else 0) + m ≤ 1)) := by
      refine ⟨fun hlt => ?_, fun heq => ?_⟩
      · have := hcrit.1 (by omega)
        omega
      · have ⟨hm1, hsum⟩ := hcrit.2 (by omega)
        refine ⟨hm1, ?_⟩
        have : (if 1 ≤ b2 then 1 else 0) = 0 := by simp [hb2]
        have : (if 1 ≤ b3 then 1 else 0) = 0 := by simp [hb3]
        omega
    have hebm := saturated_small_shore_three_c_vertices_pool_card_eq k c m eb b0 b1 c0 d
      hc hkc heb hroot' htotal' hb' hrep0' hcut' hcrit'
    have hm0 := hpool hebm
    omega
  · have hc2 : c2 = 1 := by
      by_contra hc2_ne
      have : c2 = 0 := by omega
      have hc3 : c3 = 2 := by omega
      have ⟨hc3_1, _⟩ := hsingle3 (by omega)
      omega
    have hc3 : c3 = 1 := by omega
    have ⟨_, hb21⟩ := hsingle2 (by omega)
    have hb2 : b2 = 0 := by omega
    have ⟨_, hb31⟩ := hsingle3 (by omega)
    have hb3 : b3 = 0 := by omega
    have htotal' : b0 + b1 + eb + c0 + d + m + 6 = 2 * k := by
      have : (if 1 ≤ c2 then 1 else 0) = 1 := by simp [hc2]
      have : (if 1 ≤ c3 then 1 else 0) = 1 := by simp [hc3]
      omega
    have hrep' : b0 + b1 + eb + c0 + 6 ≤ c := by
      have := hrep2C (by omega)
      omega
    have hcut' : 1 ≤ d → d + b1 + eb + c ≤ 2 * k := by
      intro hd
      have := hcutD hd
      omega
    have ⟨hebm, hb10⟩ := saturated_small_shore_two_exceptional_singletons_pool_card_eq
      k c m eb b0 b1 c0 d hkc heb htotal' hrep' hcut'
    have hm0 := hpool hebm
    have heb0 : eb = 0 := by omega
    refine ⟨hm0, heb0, hb10, hc1_1, hc2, hc3⟩
