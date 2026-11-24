import AFTD.Prelude
import AFTD.Kb.Tcs.FiveOddSaturatedLargeShoreArithmeticCore

/-!
# five_odd_saturated_large_shore_aggregate_pattern

Topic: graphs   Node: baa4eaf72109

Provenance: helper lemma. OP-1957: unbounded aggregate integer reduction for the saturated five-by-odd large-shore branch.

The displayed nonnegative aggregate component counts, endpoint budgets, degree bounds, separator inequalities and B-block odd-group inequalities force at least two C vertices outside the A-rich first component, assuming that component has three or four A vertices. The parameter m permits arbitrarily many additional odd B-only components.
-/

set_option maxHeartbeats 3000000

theorem five_odd_saturated_large_shore_aggregate_pattern
    (k c m eb : ℕ) (g : Fin 4 → Fin 4 → ℕ)
    (hc : 7 ≤ c) (hkc : c ≤ k)
    (hEB : m ≤ eb)
    (hzero : ∀ j : Fin 4, j ≠ 0 → g j 0 = 0 ∧ g j 3 = 0)
    (hgroup0 : Odd (∑ b : Fin 4, g 0 b))
    (hgroup1 : Odd (∑ b : Fin 4, g 1 b))
    (hgroupE : ∀ j : Fin 4, j = 2 ∨ j = 3 →
      (g j 2 = 0 ∧ g j 1 = 0) ∨ 1 ≤ g j 2)
    (hroot : 3 ≤ g 0 0 ∧ g 0 0 ≤ 4 ∧ 1 ≤ g 1 2)
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
    2 ≤ g 1 2 + g 2 2 + g 3 2 := by
  classical
  by_contra hn
  have hc1 : g 1 2 = 1 := by omega
  have hc2 : g 2 2 = 0 := by omega
  have hc3 : g 3 2 = 0 := by omega
  have hb2 : g 2 1 = 0 := by
    rcases hgroupE 2 (Or.inl rfl) with h | h
    · exact h.2
    · omega
  have hb3 : g 3 1 = 0 := by
    rcases hgroupE 3 (Or.inr rfl) with h | h
    · exact h.2
    · omega
  have hz10 := (hzero 1 (by decide)).1
  have hz20 := (hzero 2 (by decide)).1
  have hz30 := (hzero 3 (by decide)).1
  have hz13 := (hzero 1 (by decide)).2
  have hz23 := (hzero 2 (by decide)).2
  have hz33 := (hzero 3 (by decide)).2
  have e0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have e1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have e3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  have ha := hroot
  have ho : Odd (g 0 0 + g 0 1 + g 0 2 + g 0 3) := by
    simpa [Fin.sum_univ_four] using hgroup0
  have ht : g 0 0 + g 0 1 + g 1 1 + eb + g 0 2 + 1 + g 0 3 + m = 2*k := by
    have hh := hcounts.2.2.2.1
    simp [Fin.sum_univ_four, hc1,hc2,hc3,hb2,hb3,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hb : g 0 1 + g 1 1 + eb + 5 ≤ 2*k := by
    have hh := hcounts.2.2.1 (1 : Fin 4)
    simp [Fin.sum_univ_four, hb2,hb3] at hh
    omega
  have hry : g 0 0 + g 0 1 + g 0 2 + eb + 2 ≤ c := by
    have hh := hcounts.2.2.2.2.2.2
    simp [e1, Fin.sum_univ_four, hc1,hc2,hc3,hb2,hb3,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hrb : 1 ≤ g 0 1 → g 1 1 + eb + 9 ≤ 2*k := by
    intro h
    have hh := hrep 0 1 (by simpa using h)
    dsimp at hh
    simp [e0, e1, e3, Fin.sum_univ_four, hc1,hc2,hc3,hb2,hb3,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hrc : 1 ≤ g 0 2 → g 1 1 + eb + 4 ≤ c := by
    intro h
    have hh := hrep 0 2 (by simpa using h)
    dsimp at hh
    simp [e0, e1, e3, Fin.sum_univ_four, hc1,hc2,hc3,hb2,hb3,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hcd : 1 ≤ g 0 3 → g 0 3 + g 1 1 + eb + c ≤ 2*k := by
    intro h
    have hh := hcuts.1 0 3 (Or.inr rfl) h
    dsimp at hh
    simp [e0, e1, e3, Fin.sum_univ_four, hc1,hc2,hc3,hb2,hb3,hz10,hz20,hz30,hz13,hz23,hz33] at hh
    omega
  have hcrit' : (g 0 1 + g 1 1 + eb + 5 < 2*k → m + g 0 1 + g 1 1 + eb + 6 ≤ 2*k) ∧
    (g 0 1 + g 1 1 + eb + 5 = 2*k → m ≤ 1 ∧
      (if 1 ≤ g 0 1 then 1 else 0) + (if 1 ≤ g 1 1 then 1 else 0) + m ≤ 1) := by
    constructor
    · intro h
      have hh := hcrit.1
      simp [Fin.sum_univ_four, hb2,hb3] at hh
      have hh' := hh (by omega)
      omega
    · intro h
      have hh := hcrit.2
      dsimp at hh
      simp only [Fin.sum_univ_four] at hh
      simp [Fin.sum_univ_four, hb2,hb3] at hh
      have hh' := hh (by omega)
      exact hh'
  exact five_odd_saturated_large_shore_arithmetic_core k c m eb (g 0 0) (g 0 1) (g 1 1)
    (g 0 2) (g 0 3) hc hkc hEB ⟨ha.1,ha.2.1⟩ ho hb ht hry hrb hrc hcd hcrit'
