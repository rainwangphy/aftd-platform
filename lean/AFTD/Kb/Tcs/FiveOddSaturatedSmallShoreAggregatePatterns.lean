import AFTD.Prelude

/-!
# five_odd_saturated_small_shore_aggregate_patterns

Topic: graphs   Node: 0f301ed230c2

Provenance: helper lemma. OP-1957: unbounded aggregate integer reduction for the saturated five-by-odd small-shore branch.

The displayed nonnegative aggregate component counts, endpoint budgets, representative degree bounds, separator inequalities, and B-block odd-group inequalities imply one of the two displayed grouped small-shore patterns. The parameter m permits arbitrarily many additional odd B-only components.
-/

set_option maxHeartbeats 2000000
private theorem in1158_small_odd_endpoint_arithmetic
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

theorem five_odd_saturated_small_shore_aggregate_patterns
    (k c m eb : ℕ) (g : Fin 4 → Fin 4 → ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k)
    (hEB : m ≤ eb)
    (hzero : ∀ j : Fin 4, j ≠ 0 → g j 0 = 0 ∧ g j 3 = 0)
    (hgroup0 : Odd (∑ b : Fin 4, g 0 b))
    (hgroup1 : Odd (∑ b : Fin 4, g 1 b))
    (hgroupE : ∀ j : Fin 4, j = 2 ∨ j = 3 →
      (g j 2 = 0 ∧ g j 1 = 0) ∨ 1 ≤ g j 2)
    (hroot : 1 ≤ g 0 0 ∧ g 0 0 ≤ 2 ∧ 1 ≤ g 1 2)
    (hcounts : let s := m + (if 1 ≤ g 2 2 then 1 else 0) + (if 1 ≤ g 3 2 then 1 else 0);
      let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      s+1 ≤ c ∧ s+1 ≤ k ∧ (∀ b, tot b ≤ sz b) ∧
      (∑ b : Fin 4, tot b) + s = 2*k ∧ g 1 2 + g 2 2 + g 3 2 ≤ 3 ∧
      (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase 0, (g j 0 + g j 2 + g j 3)) ≤ 3 ∧
      (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase 1, (g j 0 + g j 1 + g j 2)) + eb + 2 ≤ c)
    (hrep : let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let forbid : Fin 4 → Fin 4 := ![1,0,3,2];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      ∀ j b : Fin 4,
        (if (j = 0 ∧ b = 0) ∨ (j = 1 ∧ b = 2) then 2 else 1) ≤ g j b →
        (∑ t ∈ (Finset.univ : Finset (Fin 4)).erase (forbid b), (tot t - g j t)) + 3 ≤ sz b)
    (hcuts : let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      (∀ j b : Fin 4, (b = 1 ∨ b = 3) → 1 ≤ g j b →
        g j b + (tot 1 - g j 1) + (tot 3 - g j 3) ≤ sz b) ∧
      (m > 0 → tot 1 + tot 3 ≤ sz 1) ∧
      (∀ j : Fin 4,
        (1 ≤ g j 0 - (if j = 0 then 1 else 0) →
          g j 0 - (if j = 0 then 1 else 0) + (tot 3 - g j 3) ≤ 5) ∧
        (1 ≤ g j 2 - (if j = 1 then 1 else 0) →
          g j 2 - (if j = 1 then 1 else 0) + (tot 1 - g j 1) ≤ c) ∧
        (1 ≤ tot 0 - g j 0 - (if j = 1 then 1 else 0) →
          g j 0 + g j 2 + g j 3 + (tot 0 - g j 0 - (if j = 1 then 1 else 0)) ≤ 5 + (tot 1 - g j 1)) ∧
        (1 ≤ tot 2 - g j 2 - (if j = 0 then 1 else 0) →
          g j 0 + g j 1 + g j 2 + (tot 2 - g j 2 - (if j = 0 then 1 else 0)) ≤ c + (tot 3 - g j 3))))
    (hcrit : let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      let groups : Fin 4 → ℕ := fun b => (∑ j : Fin 4, if 1 ≤ g j b then 1 else 0) + (if b = 1 then m else 0);
      (tot 1 < sz 1 → m + tot 1 + 1 ≤ sz 1) ∧
        (tot 1 = sz 1 → m ≤ 1 ∧ groups 1 ≤ 1))
    (hconnected : (g 0 0 = 1 → g 0 2 + g 0 3 = 0 → g 0 1 = 0) ∧
      (g 1 2 = 1 → g 1 0 + g 1 1 = 0 → g 1 3 = 0)) :
    g 0 0 = 1 ∧
      ((g 1 2 = 3 ∧ g 2 2 + g 3 2 = 0 ∧
        (g 0 1 + g 0 2 + g 2 1 + g 2 2 + g 3 1 + g 3 2 + eb) + 4 = c) ∨
       (g 1 2 = 1 ∧ g 2 2 + g 3 2 = 2 ∧
        (∀ j : Fin 4, j = 2 ∨ j = 3 → 1 ≤ g j 2 → g j 2 = 1 ∧ (∑ b : Fin 4, g j b) = 1))) := by
  classical
  have hz10 := (hzero 1 (by decide)).1
  have hz20 := (hzero 2 (by decide)).1
  have hz30 := (hzero 3 (by decide)).1
  have hz13 := (hzero 1 (by decide)).2
  have hz23 := (hzero 2 (by decide)).2
  have hz33 := (hzero 3 (by decide)).2
  have e0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have e1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have e3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  have ho0 : Odd (g 0 0 + g 0 1 + g 0 2 + g 0 3) := by simpa [Fin.sum_univ_four] using hgroup0
  have ho1 : Odd (g 1 1 + g 1 2) := by simpa [Fin.sum_univ_four,hz10,hz13] using hgroup1
  have he2 : (g 2 2=0 ∧ g 2 1=0) ∨ 1 ≤ g 2 2 := hgroupE 2 (Or.inl rfl)
  have he3 : (g 3 2=0 ∧ g 3 1=0) ∨ 1 ≤ g 3 2 := hgroupE 3 (Or.inr rfl)
  have hs : m + (if 1 ≤ g 2 2 then 1 else 0) + (if 1 ≤ g 3 2 then 1 else 0) + 1 ≤ c := hcounts.1
  have hb : g 0 1+g 1 1+g 2 1+g 3 1+eb+5 ≤ 2*k := by
    have hh := hcounts.2.2.1 (1 : Fin 4)
    simp [Fin.sum_univ_four] at hh
    omega
  have ht : g 0 0+g 0 1+g 1 1+g 2 1+g 3 1+eb+g 0 2+g 1 2+g 2 2+g 3 2+g 0 3+m+
      (if 1 ≤ g 2 2 then 1 else 0)+(if 1 ≤ g 3 2 then 1 else 0)=2*k := by
    have hh := hcounts.2.2.2.1
    simp [Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hsmall : g 1 2+g 2 2+g 3 2≤3 := hcounts.2.2.2.2.1
  have hry : g 0 0+g 0 1+g 0 2+g 2 1+g 2 2+g 3 1+g 3 2+eb+2≤c := by
    have hh := hcounts.2.2.2.2.2.2
    simp [e1,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hrA : 2≤g 0 0 → g 1 2+g 2 2+g 3 2≤2 := by
    intro h
    have hh := hrep 0 0 (by simpa using h)
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hr0 : 1≤g 0 2 → g 1 1+g 2 1+g 3 1+eb+g 1 2+g 2 2+g 3 2+3≤c := by
    intro h
    have hh := hrep 0 2 (by simpa using h)
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hcd : 1≤g 0 3 → g 0 3+g 1 1+g 2 1+g 3 1+eb+c≤2*k := by
    intro h
    have hh := hcuts.1 0 3 (Or.inr rfl) h
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hr1 : 2≤g 1 2 → g 0 0+g 0 1+g 2 1+g 3 1+eb+g 0 2+g 2 2+g 3 2+3≤c := by
    intro h
    have hh := hrep 1 2 (by simpa using h)
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hr2 : 1≤g 2 2 → g 0 0+g 0 1+g 1 1+g 3 1+eb+g 0 2+g 1 2+g 3 2+3≤c := by
    intro h
    have hh := hrep 2 2 (by simpa using h)
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hr3 : 1≤g 3 2 → g 0 0+g 0 1+g 1 1+g 2 1+eb+g 0 2+g 1 2+g 2 2+3≤c := by
    intro h
    have hh := hrep 3 2 (by simpa using h)
    dsimp at hh
    simp [e0,e1,e3,Fin.sum_univ_four,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hcrit' : (g 0 1+g 1 1+g 2 1+g 3 1+eb+5<2*k →
      m+g 0 1+g 1 1+g 2 1+g 3 1+eb+6≤2*k) ∧
    (g 0 1+g 1 1+g 2 1+g 3 1+eb+5=2*k → m≤1 ∧
      (if 1≤g 0 1 then 1 else 0)+(if 1≤g 1 1 then 1 else 0)+
      (if 1≤g 2 1 then 1 else 0)+(if 1≤g 3 1 then 1 else 0)+m≤1) := by
    constructor
    · intro h
      have hh := hcrit.1
      simp [Fin.sum_univ_four] at hh
      have hh' := hh (by omega)
      omega
    · intro h
      have hh := hcrit.2
      dsimp at hh
      simp only [Fin.sum_univ_four] at hh
      exact hh (by omega)
  have hr := in1158_small_odd_endpoint_arithmetic k c m eb (g 0 0) (g 0 1) (g 1 1) (g 2 1) (g 3 1)
    (g 0 2) (g 1 2) (g 2 2) (g 3 2) (g 0 3) hc hkc hEB ⟨hroot.1,hroot.2.1⟩
    hroot.2.2 he2 he3 ho0 ho1 hs hb ht hsmall hry hrA hr0 hcd hr1 hr2 hr3 hcrit' hconnected.1
  rcases hr with ⟨ha, hcase | hcase⟩
  · exact ⟨ha,Or.inl hcase⟩
  · refine ⟨ha, Or.inr ⟨hcase.1,hcase.2.1,?_⟩⟩
    intro j hj hjpos
    rcases hj with rfl | rfl
    · have hh := hcase.2.2.1 hjpos
      simp [Fin.sum_univ_four,hz20,hz23]
      omega
    · have hh := hcase.2.2.2 hjpos
      simp [Fin.sum_univ_four,hz30,hz33]
      omega
