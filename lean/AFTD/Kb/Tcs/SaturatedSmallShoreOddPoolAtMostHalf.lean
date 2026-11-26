import AFTD.Prelude

/-!
# saturated_small_shore_odd_pool_at_most_half

Topic: graphs   Node: 48c9911bedc4

Provenance: helper lemma. OP-1957; arithmetic consequence of the proposed large-independent-set count inequality.

Under the displayed small-shore patterns, counts, degree and separator inequalities, and the proposed large-pool count condition, the B-only group count is at most k/2.
-/

set_option maxHeartbeats 2000000

theorem saturated_small_shore_odd_pool_at_most_half
    (k c m eb a b0 b1 b2 b3 c0 c1 c2 c3 d : ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k) (heb : m ≤ eb)
    (hpat : a=1 ∧ ((c1=3 ∧ c2+c3=0 ∧ b0+c0+b2+c2+b3+c3+eb+4=c) ∨
      (c1=1 ∧ c2+c3=2 ∧ (1 ≤ c2 → c2=1 ∧ b2+c2=1) ∧
        (1 ≤ c3 → c3=1 ∧ b3+c3=1))))
    (he2 : (c2=0 ∧ b2=0) ∨ 1 ≤ c2)
    (he3 : (c3=0 ∧ b3=0) ∨ 1 ≤ c3)
    (hs : m + (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + 1 ≤ c)
    (hb : b0+b1+b2+b3+eb+5 ≤ 2*k)
    (htotal : a+b0+b1+b2+b3+eb+c0+c1+c2+c3+d+m+
      (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) = 2*k)
    (hrep0C : 1 ≤ c0 → b1+b2+b3+eb+c1+c2+c3+3 ≤ c)
    (hcutD : 1 ≤ d → d+b1+b2+b3+eb+c ≤ 2*k)
    (hrep2C : 1 ≤ c2 → a+b0+b1+b3+eb+c0+c1+c3+3 ≤ c)
    (hrep3C : 1 ≤ c3 → a+b0+b1+b2+eb+c0+c1+c2+3 ≤ c)
    (hcrit : (b0+b1+b2+b3+eb+5 < 2*k →
        m+b0+b1+b2+b3+eb+6 ≤ 2*k) ∧
      (b0+b1+b2+b3+eb+5 = 2*k → m ≤ 1))
    (hnew : k < 2*m → m+5 ≤
      (if 1 ≤ c2 then 1 else 0) + (if 1 ≤ c3 then 1 else 0) + eb+a) :
    2*m ≤ k := by
  by_contra hn
  have hm : k < 2*m := by omega
  have hnew' := hnew hm
  rcases hpat with ⟨ha,hpat | hpat⟩
  · obtain ⟨hc1,hc23,heq⟩ := hpat
    have hc2 : c2=0 := by omega
    have hc3 : c3=0 := by omega
    have hb2 : b2=0 := by rcases he2 with h | h <;> omega
    have hb3 : b3=0 := by rcases he3 with h | h <;> omega
    simp [ha,hc1,hc2,hc3,hb2,hb3] at hnew' htotal hb hs hrep0C hcutD hcrit heq
    have hd : d=0 := by
      by_contra hh
      have hx := hcutD (by omega)
      omega
    have hless : b0+b1+eb+5 < 2*k := by
      by_contra hh
      have hx := hcrit.2 (by omega)
      omega
    have hcritical := hcrit.1 hless
    have hc0 : 1 ≤ c0 := by omega
    have hrep := hrep0C hc0
    omega
  · obtain ⟨hc1,hc23,hc2,hc3⟩ := hpat
    have hc2p : 1 ≤ c2 := by
      by_contra hn2
      have h3 : 1 ≤ c3 := by omega
      have hh := hc3 h3
      omega
    have hc3p : 1 ≤ c3 := by
      by_contra hn3
      have hh := hc2 hc2p
      omega
    obtain ⟨hc2eq,hb2eq⟩ := hc2 hc2p
    obtain ⟨hc3eq,hb3eq⟩ := hc3 hc3p
    have hb2 : b2=0 := by omega
    have hb3 : b3=0 := by omega
    have hr := hrep2C hc2p
    simp [ha,hc1,hc2eq,hc3eq,hb2,hb3] at hnew' htotal hs hcutD hr
    have hd : d=0 := by
      by_contra hh
      have hx := hcutD (by omega)
      omega
    omega
