import AFTD.Prelude
import AFTD.Kb.Tcs.HnGraph
import AFTD.Kb.Tcs.HnPoly
import AFTD.Kb.Tcs.HnQuotientMatrix
import AFTD.Kb.Tcs.HnQuotientMatrixCharpoly
import AFTD.Kb.Tcs.HnPolyThreeRoots

/-!
# hn_spectrum

Topic: graphs   Node: 652c694c3ed4

Provenance: formalization of a published result. Source: arXiv:2610.18636 Theorem 4

For every integer n ≥ 2, there exist real numbers l1 > l2 > l3 such that 1/2 < l1 < 2n, 0 < l2 < 1/2, -n < l3 < 0, hn_poly n = (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) * (Polynomial.X - Polynomial.C l3), and the characteristic polynomial of the real adjacency matrix of the competitor graph hn_graph n equals Polynomial.X ^ (3 * n - 4) * (Polynomial.X + Polynomial.C (n : ℝ)) * hn_poly n.
-/

open scoped Classical in
def hn_spectrum_cell (n : ℕ) (v : Fin (3 * n)) : Fin 4 :=
  if v.val < n - 1 then 0
  else if v.val < 2 * n - 1 then 1
  else if v.val < 3 * n - 1 then 2
  else 3

def hn_spectrum_cell_size (n : ℕ) (k : Fin 4) : ℕ := ![n - 1, n, n, 1] k

noncomputable def hn_spectrum_U (n : ℕ) : Matrix (Fin (3*n)) (Fin 4) ℝ :=
  fun v k => if hn_spectrum_cell n v = k then 1 else 0

noncomputable def hn_spectrum_D (n : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun k => (hn_spectrum_cell_size n k : ℝ))

def hn_spectrum_M : Matrix (Fin 4) (Fin 4) ℝ := !![0,1,1,1; 1,0,1,0; 1,1,0,0; 1,0,0,0]

lemma hn_spectrum_cell_eq_zero_iff {n : ℕ} (v : Fin (3 * n)) :
    hn_spectrum_cell n v = 0 ↔ v.val < n - 1 := by
  unfold hn_spectrum_cell
  split_ifs with h1 h2 h3 <;> simp_all

lemma hn_spectrum_cell_eq_one_iff {n : ℕ} (v : Fin (3 * n)) :
    hn_spectrum_cell n v = 1 ↔ n - 1 ≤ v.val ∧ v.val < 2 * n - 1 := by
  unfold hn_spectrum_cell
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

lemma hn_spectrum_cell_eq_two_iff {n : ℕ} (v : Fin (3 * n)) :
    hn_spectrum_cell n v = 2 ↔ 2 * n - 1 ≤ v.val ∧ v.val < 3 * n - 1 := by
  unfold hn_spectrum_cell
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

lemma hn_spectrum_cell_eq_three_iff {n : ℕ} (v : Fin (3 * n)) :
    hn_spectrum_cell n v = 3 ↔ v.val = 3 * n - 1 := by
  unfold hn_spectrum_cell
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

lemma hn_spectrum_rel_iff (n : ℕ) (u v : Fin (3 * n)) :
    ((u.val < n - 1 ∧ v.val ≥ n - 1) ∨
      (n - 1 ≤ u.val ∧ u.val < 2 * n - 1 ∧ 2 * n - 1 ≤ v.val ∧ v.val < 3 * n - 1))
    ↔ (hn_spectrum_cell n u = 0 ∧ hn_spectrum_cell n v ≠ 0) ∨
      (hn_spectrum_cell n u = 1 ∧ hn_spectrum_cell n v = 2) := by
  have hv0 : hn_spectrum_cell n v ≠ 0 ↔ v.val ≥ n - 1 := by
    rw [Ne, hn_spectrum_cell_eq_zero_iff]; omega
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨(hn_spectrum_cell_eq_zero_iff u).mpr h1, hv0.mpr h2⟩
    · exact Or.inr ⟨(hn_spectrum_cell_eq_one_iff u).mpr ⟨h1, h2⟩,
        (hn_spectrum_cell_eq_two_iff v).mpr ⟨h3, h4⟩⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨(hn_spectrum_cell_eq_zero_iff u).mp h1, hv0.mp h2⟩
    · obtain ⟨a, b⟩ := (hn_spectrum_cell_eq_one_iff u).mp h1
      obtain ⟨c, d⟩ := (hn_spectrum_cell_eq_two_iff v).mp h2
      exact Or.inr ⟨a, b, c, d⟩

lemma hn_spectrum_M_eq_one_iff (a b : Fin 4) :
    hn_spectrum_M a b = 1 ↔
      (a = 0 ∧ b ≠ 0) ∨ (a = 1 ∧ b = 2) ∨ (b = 0 ∧ a ≠ 0) ∨ (b = 1 ∧ a = 2) := by
  fin_cases a <;> fin_cases b <;> simp [hn_spectrum_M]

lemma hn_spectrum_M_diag (a : Fin 4) : hn_spectrum_M a a = 0 := by
  fin_cases a <;> simp [hn_spectrum_M]

lemma hn_spectrum_M_eq_zero_or_one (a b : Fin 4) :
    hn_spectrum_M a b = 0 ∨ hn_spectrum_M a b = 1 := by
  fin_cases a <;> fin_cases b <;> simp [hn_spectrum_M]

lemma hn_spectrum_adj_iff_M (n : ℕ) (v w : Fin (3 * n)) :
    (hn_graph n).Adj v w ↔ hn_spectrum_M (hn_spectrum_cell n v) (hn_spectrum_cell n w) = 1 := by
  have h1 := hn_spectrum_rel_iff n v w
  have h2 := hn_spectrum_rel_iff n w v
  have hM := hn_spectrum_M_eq_one_iff (hn_spectrum_cell n v) (hn_spectrum_cell n w)
  simp only [hn_graph, SimpleGraph.fromRel]
  constructor
  · rintro ⟨-, h | h⟩
    · rcases h1.mp h with ⟨a, b⟩ | ⟨a, b⟩
      · exact hM.mpr (Or.inl ⟨a, b⟩)
      · exact hM.mpr (Or.inr (Or.inl ⟨a, b⟩))
    · rcases h2.mp h with ⟨a, b⟩ | ⟨a, b⟩
      · exact hM.mpr (Or.inr (Or.inr (Or.inl ⟨a, b⟩)))
      · exact hM.mpr (Or.inr (Or.inr (Or.inr ⟨a, b⟩)))
  · intro hm
    have hcne : hn_spectrum_cell n v ≠ hn_spectrum_cell n w := by
      intro hab
      rw [hab, hn_spectrum_M_diag] at hm
      exact zero_ne_one hm
    refine ⟨fun he => hcne (by rw [he]), ?_⟩
    rcases hM.mp hm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl (h1.mpr (Or.inl ⟨a, b⟩))
    · exact Or.inl (h1.mpr (Or.inr ⟨a, b⟩))
    · exact Or.inr (h2.mpr (Or.inl ⟨a, b⟩))
    · exact Or.inr (h2.mpr (Or.inr ⟨a, b⟩))

lemma hn_spectrum_U_M_apply (n : ℕ) (v : Fin (3*n)) (k : Fin 4) :
    (hn_spectrum_U n * hn_spectrum_M) v k = hn_spectrum_M (hn_spectrum_cell n v) k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (hn_spectrum_cell n v)]
  · simp [hn_spectrum_U]
  · intro l _ hl; simp [hn_spectrum_U, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma hn_spectrum_U_M_U_transpose_apply (n : ℕ) (v w : Fin (3*n)) :
    (hn_spectrum_U n * hn_spectrum_M * Matrix.transpose (hn_spectrum_U n)) v w
      = hn_spectrum_M (hn_spectrum_cell n v) (hn_spectrum_cell n w) := by
  rw [Matrix.mul_apply]
  simp only [hn_spectrum_U_M_apply, Matrix.transpose_apply]
  rw [Finset.sum_eq_single (hn_spectrum_cell n w)]
  · simp [hn_spectrum_U]
  · intro l _ hl; simp [hn_spectrum_U, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped Classical in
lemma hn_spectrum_adjMatrix_eq (n : ℕ) (hle : 2 ≤ n) :
    SimpleGraph.adjMatrix ℝ (hn_graph n)
      = hn_spectrum_U n * hn_spectrum_M * Matrix.transpose (hn_spectrum_U n) := by
  ext v w
  rw [hn_spectrum_U_M_U_transpose_apply]
  simp only [SimpleGraph.adjMatrix, Matrix.of_apply]
  by_cases h : (hn_graph n).Adj v w
  · rw [if_pos h]
    exact ((hn_spectrum_adj_iff_M n v w).mp h).symm
  · rw [if_neg h]
    have hne : hn_spectrum_M (hn_spectrum_cell n v) (hn_spectrum_cell n w) ≠ 1 :=
      fun hc => h ((hn_spectrum_adj_iff_M n v w).mpr hc)
    rcases hn_spectrum_M_eq_zero_or_one (hn_spectrum_cell n v) (hn_spectrum_cell n w) with h0 | h1
    · exact h0.symm
    · exact absurd h1 hne

lemma hn_spectrum_fin_card_val_lt {m a : ℕ} (h : a ≤ m) :
    Fintype.card {v : Fin m // v.val < a} = a := by
  have e : {v : Fin m // v.val < a} ≃ Fin a :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.val, lt_of_lt_of_le y.isLt h⟩, y.isLt⟩
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  rw [Fintype.card_congr e]; simp

lemma hn_spectrum_fin_card_val_between {m a b : ℕ} (h1 : a ≤ b) (h2 : b ≤ m) :
    Fintype.card {v : Fin m // a ≤ v.val ∧ v.val < b} = b - a := by
  have e : {v : Fin m // a ≤ v.val ∧ v.val < b} ≃ Fin (b - a) :=
    { toFun := fun x => ⟨x.1.val - a, by have := x.2.1; have := x.2.2; omega⟩
      invFun := fun y => ⟨⟨y.val + a, by have := y.isLt; omega⟩, by
        have := y.isLt; show a ≤ y.val + a ∧ y.val + a < b; constructor <;> omega⟩
      left_inv := by
        intro x; apply Subtype.ext; apply Fin.ext; simp only
        exact Nat.sub_add_cancel x.2.1
      right_inv := by
        intro y; apply Fin.ext; simp only
        exact Nat.add_sub_cancel_right y.val a }
  rw [Fintype.card_congr e]; simp

lemma hn_spectrum_fin_card_val_eq {m a : ℕ} (h : a < m) :
    Fintype.card {v : Fin m // v.val = a} = 1 := by
  have e : {v : Fin m // v.val = a} ≃ Fin 1 :=
    { toFun := fun _ => ⟨0, by omega⟩
      invFun := fun _ => ⟨⟨a, h⟩, rfl⟩
      left_inv := by intro x; apply Subtype.ext; apply Fin.ext; exact x.2.symm
      right_inv := by intro y; apply Fin.ext; simp }
  rw [Fintype.card_congr e]; simp

lemma hn_spectrum_card_cell_zero (n : ℕ) :
    (Finset.univ.filter (fun v : Fin (3*n) => hn_spectrum_cell n v = 0)).card = n - 1 := by
  rw [← Fintype.card_subtype (fun v : Fin (3*n) => hn_spectrum_cell n v = 0)]
  have e : {v : Fin (3*n) // hn_spectrum_cell n v = 0} ≃ {v : Fin (3*n) // v.val < n - 1} :=
    { toFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_zero_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_zero_iff x.1).mpr x.2⟩
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  rw [Fintype.card_congr e]
  exact hn_spectrum_fin_card_val_lt (by omega)

lemma hn_spectrum_card_cell_one (n : ℕ) :
    (Finset.univ.filter (fun v : Fin (3*n) => hn_spectrum_cell n v = 1)).card = n := by
  rw [← Fintype.card_subtype (fun v : Fin (3*n) => hn_spectrum_cell n v = 1)]
  have e : {v : Fin (3*n) // hn_spectrum_cell n v = 1} ≃
      {v : Fin (3*n) // n - 1 ≤ v.val ∧ v.val < 2 * n - 1} :=
    { toFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_one_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_one_iff x.1).mpr x.2⟩
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  rw [Fintype.card_congr e]
  rw [hn_spectrum_fin_card_val_between (by omega) (by omega)]
  omega

lemma hn_spectrum_card_cell_two (n : ℕ) :
    (Finset.univ.filter (fun v : Fin (3*n) => hn_spectrum_cell n v = 2)).card = n := by
  rw [← Fintype.card_subtype (fun v : Fin (3*n) => hn_spectrum_cell n v = 2)]
  have e : {v : Fin (3*n) // hn_spectrum_cell n v = 2} ≃
      {v : Fin (3*n) // 2 * n - 1 ≤ v.val ∧ v.val < 3 * n - 1} :=
    { toFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_two_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_two_iff x.1).mpr x.2⟩
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  rw [Fintype.card_congr e]
  rw [hn_spectrum_fin_card_val_between (by omega) (by omega)]
  omega

lemma hn_spectrum_card_cell_three (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun v : Fin (3*n) => hn_spectrum_cell n v = 3)).card = 1 := by
  rw [← Fintype.card_subtype (fun v : Fin (3*n) => hn_spectrum_cell n v = 3)]
  have e : {v : Fin (3*n) // hn_spectrum_cell n v = 3} ≃ {v : Fin (3*n) // v.val = 3 * n - 1} :=
    { toFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_three_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hn_spectrum_cell_eq_three_iff x.1).mpr x.2⟩
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  rw [Fintype.card_congr e]
  exact hn_spectrum_fin_card_val_eq (by omega)

lemma hn_spectrum_card_cell (n : ℕ) (hn : 1 ≤ n) (k : Fin 4) :
    (Finset.univ.filter (fun v : Fin (3*n) => hn_spectrum_cell n v = k)).card
      = hn_spectrum_cell_size n k := by
  fin_cases k
  · simpa [hn_spectrum_cell_size] using hn_spectrum_card_cell_zero n
  · simpa [hn_spectrum_cell_size] using hn_spectrum_card_cell_one n
  · simpa [hn_spectrum_cell_size] using hn_spectrum_card_cell_two n
  · simpa [hn_spectrum_cell_size] using hn_spectrum_card_cell_three n hn

lemma hn_spectrum_sum_ite_ite (n : ℕ) (k l : Fin 4) :
    (∑ v : Fin (3*n),
        (if hn_spectrum_cell n v = k then (1:ℝ) else 0) *
          (if hn_spectrum_cell n v = l then 1 else 0))
      = if k = l then ((Finset.univ.filter (fun v => hn_spectrum_cell n v = k)).card : ℝ) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, ← Finset.sum_boole (fun v => hn_spectrum_cell n v = k) Finset.univ]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : hn_spectrum_cell n v = k <;> simp [h]
  · rw [if_neg hkl]
    apply Finset.sum_eq_zero
    intro v _
    by_cases h : hn_spectrum_cell n v = k
    · simp [h, hkl]
    · simp [h]

lemma hn_spectrum_U_transpose_mul_U (n : ℕ) (hn : 1 ≤ n) :
    Matrix.transpose (hn_spectrum_U n) * hn_spectrum_U n = hn_spectrum_D n := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hn_spectrum_U, hn_spectrum_D, Matrix.diagonal, Matrix.of_apply]
  rw [hn_spectrum_sum_ite_ite]
  by_cases hkl : k = l
  · rw [if_pos hkl, if_pos hkl]
    rw [hn_spectrum_card_cell n hn k]
  · rw [if_neg hkl, if_neg hkl]

lemma hn_spectrum_M_mul_D (n : ℕ) (hn : 1 ≤ n) :
    hn_spectrum_M * hn_spectrum_D n = hn_quotient_matrix n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hn_spectrum_M, hn_spectrum_D, hn_spectrum_cell_size, hn_quotient_matrix,
      Matrix.diagonal, Matrix.mul_apply]
  all_goals (rw [Nat.cast_sub hn]; ring)

open scoped Classical in
lemma hn_spectrum_adj_charpoly (n : ℕ) (hle : 2 ≤ n) :
    (SimpleGraph.adjMatrix ℝ (hn_graph n)).charpoly =
      Polynomial.X ^ (3 * n - 4) * (Polynomial.X + Polynomial.C (n : ℝ)) * hn_poly n := by
  have hn1 : 1 ≤ n := by omega
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card (Fin (3*n)) := by simp; omega
  have hA : SimpleGraph.adjMatrix ℝ (hn_graph n)
      = hn_spectrum_U n * (hn_spectrum_M * Matrix.transpose (hn_spectrum_U n)) := by
    rw [hn_spectrum_adjMatrix_eq n hle, Matrix.mul_assoc]
  have hBU : (hn_spectrum_M * Matrix.transpose (hn_spectrum_U n)) * hn_spectrum_U n
      = hn_quotient_matrix n := by
    rw [Matrix.mul_assoc, hn_spectrum_U_transpose_mul_U n hn1, hn_spectrum_M_mul_D n hn1]
  rw [hA, Matrix.charpoly_mul_comm_of_le (hn_spectrum_U n)
    (hn_spectrum_M * Matrix.transpose (hn_spectrum_U n)) hcard, hBU, hn_quotient_matrix_charpoly]
  simp only [Fintype.card_fin]
  rw [mul_assoc]

open scoped Classical in
/-- Spectrum of the complete tripartite competitor graph H_n (arXiv:2610.18636 Theorem 4). -/
theorem hn_spectrum (n : ℕ) (hle : 2 ≤ n) :
    ∃ l1 l2 l3 : ℝ,
      1 / 2 < l1 ∧ l1 < 2 * (n : ℝ) ∧
      0 < l2 ∧ l2 < 1 / 2 ∧
      -(n : ℝ) < l3 ∧ l3 < 0 ∧
      l2 < l1 ∧ l3 < l2 ∧
      hn_poly n = (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) * (Polynomial.X - Polynomial.C l3) ∧
      (SimpleGraph.adjMatrix ℝ (hn_graph n)).charpoly =
        Polynomial.X ^ (3 * n - 4) * (Polynomial.X + Polynomial.C (n : ℝ)) * hn_poly n := by
  obtain ⟨l1, l2, l3, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hn_poly_three_roots n hle
  exact ⟨l1, l2, l3, h1, h2, h3, h4, h5, h6, h7, h8, h9, hn_spectrum_adj_charpoly n hle⟩
