import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nDominationNumberFourGe
import AFTD.Kb.Tcs.F

/-!
# bipartite_complement_adj_charpoly_mul

Topic: graphs   Node: c01089840661

Provenance: helper lemma. arXiv:2611.00591, Lemma 4.1 (step of its proof)

Let H be an s-regular graph contained in the complete bipartite graph on parts V, W of size m, and G = K_{V,W} minus H. Then charpoly(A_G)·(X² − s²) = charpoly(A_H)·(X² − (m − s)²) for the real adjacency matrices.
-/

/-- the two part indicator columns -/
noncomputable def bipc_E (V W : Type*) : Matrix (V ⊕ W) (Fin 2) ℝ :=
  Matrix.of fun i c => Sum.elim (fun _ => if c = 0 then (1 : ℝ) else 0)
    (fun _ => if c = 1 then (1 : ℝ) else 0) i

noncomputable def bipc_F (V W : Type*) : Matrix (Fin 2) (V ⊕ W) ℝ :=
  Matrix.of fun c j => Sum.elim (fun _ => if c = 1 then (1 : ℝ) else 0)
    (fun _ => if c = 0 then (1 : ℝ) else 0) j

theorem bipc_FE {V W : Type*} [Fintype V] [Fintype W] (m : ℕ)
    (hV : Fintype.card V = m) (hW : Fintype.card W = m) :
    bipc_F V W * bipc_E V W = !![0, (m : ℝ); (m : ℝ), 0] := by
  ext c d
  fin_cases c <;> fin_cases d <;>
    simp [bipc_E, bipc_F, Matrix.mul_apply, Fintype.sum_sum_type, hV, hW]

theorem bipc_AE {V W : Type*} [Fintype V] [Fintype W] [DecidableEq (V ⊕ W)] (A : Matrix (V ⊕ W) (V ⊕ W) ℝ) (s : ℝ)
    (hll : ∀ v v', A (Sum.inl v) (Sum.inl v') = 0) (hrr : ∀ w w', A (Sum.inr w) (Sum.inr w') = 0)
    (hrow : ∀ i, ∑ j, A i j = s) (x : ℝ) :
    (Matrix.scalar (V ⊕ W) x - A) * bipc_E V W = bipc_E V W * !![x, -s; -s, x] := by
  ext i c
  rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_mul]
  have hrow' := hrow i
  rw [Fintype.sum_sum_type] at hrow'
  rcases i with v | w
  · simp only [hll, Finset.sum_const_zero, zero_add] at hrow'
    fin_cases c <;>
      simp [bipc_E, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.sub_apply, hll, hrow',
        Matrix.scalar_apply, Matrix.diagonal_apply]
  · simp only [hrr, Finset.sum_const_zero, add_zero] at hrow'
    fin_cases c <;>
      simp [bipc_E, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.sub_apply, hrr, hrow',
        Matrix.scalar_apply, Matrix.diagonal_apply]

theorem bipc_det_identity {V W : Type*} [Fintype V] [Fintype W] [DecidableEq (V ⊕ W)]
    (m : ℕ) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (A : Matrix (V ⊕ W) (V ⊕ W) ℝ) (s : ℝ)
    (hll : ∀ v v', A (Sum.inl v) (Sum.inl v') = 0) (hrr : ∀ w w', A (Sum.inr w) (Sum.inr w') = 0)
    (hrow : ∀ i, ∑ j, A i j = s) (x : ℝ)
    (hN : (Matrix.scalar (V ⊕ W) x - A).det ≠ 0) (hxs : x ^ 2 - s ^ 2 ≠ 0) :
    (Matrix.scalar (V ⊕ W) x - A + bipc_E V W * bipc_F V W).det * (x ^ 2 - s ^ 2) =
      (Matrix.scalar (V ⊕ W) x - A).det * (x ^ 2 - ((m : ℝ) - s) ^ 2) := by
  set N := Matrix.scalar (V ⊕ W) x - A with hNdef
  set E := bipc_E V W
  set F := bipc_F V W
  set T : Matrix (Fin 2) (Fin 2) ℝ := !![x, -s; -s, x] with hT
  have hTdet : T.det = x ^ 2 - s ^ 2 := by
    rw [hT, Matrix.det_fin_two_of]; ring
  have hNE : N * E = E * T := bipc_AE A s hll hrr hrow x
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr (by rw [hTdet]; exact hxs)
  have hinvE : N⁻¹ * E = E * T⁻¹ := by
    have h1 : N⁻¹ * (E * T) = E := by
      rw [← hNE, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hNu, Matrix.one_mul]
    calc N⁻¹ * E = N⁻¹ * E * (T * T⁻¹) := by rw [Matrix.mul_nonsing_inv _ hTu, Matrix.mul_one]
      _ = N⁻¹ * (E * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E * T⁻¹ := by rw [h1]
  have hsplit : N + E * F = N * (1 + (N⁻¹ * E) * F) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hNu, Matrix.one_mul]
  have h2 : (1 + F * (E * T⁻¹)) * T = T + F * E := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hTu, Matrix.mul_one]
  have hTFE : (T + F * E).det = x ^ 2 - ((m : ℝ) - s) ^ 2 := by
    rw [bipc_FE m hV hW, hT]
    rw [show (!![x, -s; -s, x] + !![0, (m : ℝ); (m : ℝ), 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![x, m - s; m - s, x] by
        ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring]
    rw [Matrix.det_fin_two_of]; ring
  rw [hsplit, Matrix.det_mul, Matrix.det_one_add_mul_comm, hinvE, ← hTdet, mul_assoc,
    ← Matrix.det_mul, h2, hTFE]

open scoped Classical in
theorem bipartite_complement_adj_charpoly_mul
    {V W : Type*} [Fintype V] [Fintype W]
    (m s : ℕ) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (H : SimpleGraph (V ⊕ W)) (hH_sub : H ≤ completeBipartiteGraph V W)
    (hH_reg : H.IsRegularOfDegree s) :
    ((completeBipartiteGraph V W \ H).adjMatrix ℝ).charpoly *
        (Polynomial.X ^ 2 - Polynomial.C ((s : ℝ) ^ 2)) =
      (H.adjMatrix ℝ).charpoly * (Polynomial.X ^ 2 - Polynomial.C (((m : ℝ) - s) ^ 2)) := by
  have hnl : ∀ v v', ¬ H.Adj (Sum.inl v) (Sum.inl v') := by
    intro v v' h
    have := hH_sub h
    simp at this
  have hnr : ∀ w w', ¬ H.Adj (Sum.inr w) (Sum.inr w') := by
    intro w w' h
    have := hH_sub h
    simp at this
  set A := H.adjMatrix ℝ with hA
  set Ag := (completeBipartiteGraph V W \ H).adjMatrix ℝ with hAg
  have hll : ∀ v v', A (Sum.inl v) (Sum.inl v') = 0 := by
    intro v v'
    rw [hA, SimpleGraph.adjMatrix_apply, if_neg]
    intro h
    have := hH_sub h
    simp at this
  have hrr : ∀ w w', A (Sum.inr w) (Sum.inr w') = 0 := by
    intro w w'
    rw [hA, SimpleGraph.adjMatrix_apply, if_neg]
    intro h
    have := hH_sub h
    simp at this
  have hrow : ∀ i, ∑ j, A i j = s := by
    intro i
    have := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hH_reg (a := 1) (v := i)
    simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] at this
    exact this
  set D : Matrix (V ⊕ W) (V ⊕ W) ℝ := Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
    with hDdef
  have hD2 : D * D = 1 := by
    rw [hDdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    cases i <;> simp
  have hDD : D.det * D.det = 1 := by rw [← Matrix.det_mul, hD2, Matrix.det_one]
  have hconj : ∀ x : ℝ, D * (Matrix.scalar (V ⊕ W) x - Ag) * D =
      Matrix.scalar (V ⊕ W) x - A + bipc_E V W * bipc_F V W := by
    intro x
    ext i j
    rw [hDdef, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with v | w <;> rcases j with v' | w'
    · have := hll v v'
      simp only [hA] at this
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, bipc_E, bipc_F, Matrix.mul_apply,
        Fin.sum_univ_two, hAg, hA, this, SimpleGraph.adjMatrix_apply, hnl, hnr]
      try (split_ifs <;> simp)
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        bipc_E, bipc_F, Matrix.mul_apply, Fin.sum_univ_two, hAg, hA, SimpleGraph.adjMatrix_apply,
        SimpleGraph.sdiff_adj, completeBipartiteGraph_adj]
      simp
      split_ifs <;> simp
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        bipc_E, bipc_F, Matrix.mul_apply, Fin.sum_univ_two, hAg, hA, SimpleGraph.adjMatrix_apply,
        SimpleGraph.sdiff_adj, completeBipartiteGraph_adj]
      simp
      split_ifs <;> simp
    · have := hrr w w'
      simp only [hA] at this
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, bipc_E, bipc_F, Matrix.mul_apply,
        Fin.sum_univ_two, hAg, hA, this, SimpleGraph.adjMatrix_apply, hnl, hnr]
      try (split_ifs <;> simp)
  have heval : ∀ x : ℝ, Ag.charpoly.eval x =
      (Matrix.scalar (V ⊕ W) x - A + bipc_E V W * bipc_F V W).det := by
    intro x
    rw [Matrix.eval_charpoly, ← hconj x, Matrix.det_mul, Matrix.det_mul]
    calc (Matrix.scalar (V ⊕ W) x - Ag).det
        = (D.det * D.det) * (Matrix.scalar (V ⊕ W) x - Ag).det := by rw [hDD, one_mul]
      _ = _ := by ring
  have hp : A.charpoly * (Polynomial.X ^ 2 - Polynomial.C ((s : ℝ) ^ 2)) ≠ 0 :=
    ((Matrix.charpoly_monic A).mul (Polynomial.monic_X_pow_sub_C _ (by norm_num))).ne_zero
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Polynomial.finite_setOfPred_isRoot hp).infinite_compl
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx ⊢
  rcases mul_ne_zero_iff.mp hx with ⟨h1, h2⟩
  rw [Matrix.eval_charpoly] at h1
  rw [heval x, Matrix.eval_charpoly]
  exact bipc_det_identity m hV hW A s hll hrr hrow x h1 h2
