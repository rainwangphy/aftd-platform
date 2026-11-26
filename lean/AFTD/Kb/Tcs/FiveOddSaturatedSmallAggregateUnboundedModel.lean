import AFTD.Prelude

/-!
# five_odd_saturated_small_aggregate_unbounded_model

Topic: graphs   Node: dce068ead950

Provenance: helper lemma. OP-1957; saturated barrier graph-to-count reduction.

For every t, the displayed full small-shore aggregate count hypotheses, including the earlier connectedness conditions, have an explicit solution with odd c and at least t block-only groups. This is an arithmetic model, with no assertion that it is realizable by a graph.
-/

set_option maxHeartbeats 2000000

theorem five_odd_saturated_small_aggregate_unbounded_model (t : ℕ) :
  let c := 2*t+7
  let k := c
  let m := c-4
  let eb := m
  let g : Fin 4 → Fin 4 → ℕ := ![![1,0,0,4], ![0,0,3,0], ![0,0,0,0], ![0,0,0,0]]
  Odd c ∧ t ≤ m ∧
  (7 ≤ c) ∧
  (c ≤ k) ∧
  (m ≤ eb) ∧
  (∀ j : Fin 4, j ≠ 0 → g j 0 = 0 ∧ g j 3 = 0) ∧
  (Odd (∑ b : Fin 4, g 0 b)) ∧
  (Odd (∑ b : Fin 4, g 1 b)) ∧
  (∀ j : Fin 4, j = 2 ∨ j = 3 →
      (g j 2 = 0 ∧ g j 1 = 0) ∨ 1 ≤ g j 2) ∧
  (1 ≤ g 0 0 ∧ g 0 0 ≤ 2 ∧ 1 ≤ g 1 2) ∧
  (let s := m + (if 1 ≤ g 2 2 then 1 else 0) + (if 1 ≤ g 3 2 then 1 else 0);
      let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      s+1 ≤ c ∧ s+1 ≤ k ∧ (∀ b, tot b ≤ sz b) ∧
      (∑ b : Fin 4, tot b) + s = 2*k ∧ g 1 2 + g 2 2 + g 3 2 ≤ 3 ∧
      (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase 0, (g j 0 + g j 2 + g j 3)) ≤ 3 ∧
      (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase 1, (g j 0 + g j 1 + g j 2)) + eb + 2 ≤ c) ∧
  (let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let forbid : Fin 4 → Fin 4 := ![1,0,3,2];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      ∀ j b : Fin 4,
        (if (j = 0 ∧ b = 0) ∨ (j = 1 ∧ b = 2) then 2 else 1) ≤ g j b →
        (∑ t ∈ (Finset.univ : Finset (Fin 4)).erase (forbid b), (tot t - g j t)) + 3 ≤ sz b) ∧
  (let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
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
          g j 0 + g j 1 + g j 2 + (tot 2 - g j 2 - (if j = 0 then 1 else 0)) ≤ c + (tot 3 - g j 3)))) ∧
  (let sz : Fin 4 → ℕ := ![5, 2*k-5, c, 2*k-c];
      let tot : Fin 4 → ℕ := fun b => (∑ j : Fin 4, g j b) + (if b = 1 then eb else 0);
      let groups : Fin 4 → ℕ := fun b => (∑ j : Fin 4, if 1 ≤ g j b then 1 else 0) + (if b = 1 then m else 0);
      (tot 1 < sz 1 → m + tot 1 + 1 ≤ sz 1) ∧
        (tot 1 = sz 1 → m ≤ 1 ∧ groups 1 ≤ 1)) ∧
  ((g 0 0 = 1 → g 0 2 + g 0 3 = 0 → g 0 1 = 0) ∧
   (g 1 2 = 1 → g 1 0 + g 1 1 = 0 → g 1 3 = 0)) := by
  dsimp only
  have e0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have e1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have e2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have e3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  constructor
  · exact ⟨t+3, by omega⟩
  constructor
  · omega
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    fin_cases j <;> simp_all
  · norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · intro j hj
    fin_cases j <;> simp_all
  · norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · simp [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, e0, e1, e2, e3]
    constructor
    · intro b
      fin_cases b <;> simp [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> omega
    · constructor <;> omega
  · intro j b
    fin_cases j <;> fin_cases b <;> simp [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, e0, e1, e2, e3] <;> omega
  · constructor
    · intro j b hb
      fin_cases j <;> fin_cases b <;> simp_all [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, e0, e1, e2, e3] <;> omega
    constructor
    · simp [Fin.sum_univ_four]
      omega
    · intro j
      fin_cases j <;> simp [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, e0, e1, e2, e3] <;> omega
  · simp [Fin.sum_univ_four]
    omega
  · norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
