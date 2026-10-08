import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingExistsRowStrictPair
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingExistsColStrictPair
import AFTD.Kb.GameTheoryEconomics.Strict

/-!
# EconCSLib.LinearProgramming.exists_strong_complementary_pair

Topic: lp_duality   Node: ed7347f7f90a

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.exists_strong_complementary_pair`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**LP Strong Complementarity** [MFoGT, Section 2.8, Exercise 11]: given an optimal primal-dual pair `(x₀, u₀)` with common value `v`, there exists an optimal pair `(x*, u*)` such that for **every** row `i ∈ I` and column `j ∈ Fin n`, the row complementarity sum `(Ax* - b)_i + u*_i` and the column complementarity sum `x*_j + (c - u*ᵀA)_j` are strictly positive. Combined with weak complementary slackness, this is the strict biconditional form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators EconCSLib.LinearAlgebra in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **LP Strong Complementarity** [MFoGT, Section 2.8, Exercise 11]: given an optimal primal-dual pair `(x₀, u₀)` with common value `v`, there exists an optimal pair `(x*, u*)` such that for **every** row `i ∈ I` and column `j ∈ Fin n`, the row complementarity sum `(Ax* - b)_i + u*_i` and the column complementarity sum `x*_j + (c - u*ᵀA)_j` are strictly positive. Combined with weak complementary slackness, this is the strict biconditional form. -/
theorem EconCSLib.LinearProgramming.exists_strong_complementary_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    (hN_pos : (0 : 𝕜) < ((Fintype.card I + n : ℕ) : 𝕜))
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      (∀ i, 0 < (∑ j, A i j * x j - b i) + u i) ∧
      (∀ j, 0 < x j + (c j - ∑ i, u i * A i j)) := by
  classical
  -- Skolemise per-row and per-column witnesses.
  have row_wits : ∀ i₀ : I, _ := fun i₀ =>
    exists_row_strict_pair A b c v hx₀A hx₀nn hx₀_val hu₀ hu₀_val i₀
  have col_wits : ∀ j₀ : Fin n, _ := fun j₀ =>
    exists_col_strict_pair A b c v hx₀A hx₀nn hx₀_val hu₀ hu₀_val j₀
  choose xR uR hxR_A hxR_nn huR_du hxR_cx huR_ub hR_strict using row_wits
  choose xC uC hxC_A hxC_nn huC_du hxC_cx huC_ub hC_strict using col_wits
  -- Cast N to 𝕜.
  set N : 𝕜 := ((Fintype.card I + n : ℕ) : 𝕜) with hN_def
  have hN_ne : N ≠ 0 := hN_pos.ne'
  -- Average x and u over all witnesses.
  set x_avg : Fin n → 𝕜 :=
    fun j => ((∑ i, xR i j) + (∑ j', xC j' j)) / N with hx_avg_def
  set u_avg : I → 𝕜 :=
    fun i => ((∑ i', uR i' i) + (∑ j, uC j i)) / N with hu_avg_def
  -- Cardinality identity.
  have hN_card : (Fintype.card I : 𝕜) + (n : 𝕜) = N := by
    rw [hN_def]; push_cast; ring
  -- Key linearity identities for Ax_avg, c·x_avg, u_avgᵀA, u_avg·b.
  have hAx_avg : ∀ i, (∑ j, A i j * x_avg j)
      = ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)) / N := by
    intro i
    simp only [hx_avg_def, mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ j, A i j * ((∑ i', xR i' j) + (∑ j', xC j' j)))
        = (∑ j, ∑ i', A i j * xR i' j) + (∑ j, ∑ j', A i j * xC j' j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun j j' => A i j * xC j' j)]
  have hcx_avg : (∑ j, c j * x_avg j)
      = ((∑ i', ∑ j, c j * xR i' j) + (∑ j', ∑ j, c j * xC j' j)) / N := by
    simp only [hx_avg_def, mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ j, c j * ((∑ i', xR i' j) + (∑ j', xC j' j)))
        = (∑ j, ∑ i', c j * xR i' j) + (∑ j, ∑ j', c j * xC j' j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun j j' => c j * xC j' j)]
  have huA_avg : ∀ j, (∑ i, u_avg i * A i j)
      = ((∑ i', ∑ i, uR i' i * A i j) + (∑ j', ∑ i, uC j' i * A i j)) / N := by
    intro j
    simp only [hu_avg_def, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ i, ((∑ i', uR i' i) + (∑ j', uC j' i)) * A i j)
        = (∑ i, ∑ i', uR i' i * A i j) + (∑ i, ∑ j', uC j' i * A i j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun i j' => uC j' i * A i j)]
  have hub_avg : (∑ i, u_avg i * b i)
      = ((∑ i', ∑ i, uR i' i * b i) + (∑ j', ∑ i, uC j' i * b i)) / N := by
    simp only [hu_avg_def, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ i, ((∑ i', uR i' i) + (∑ j', uC j' i)) * b i)
        = (∑ i, ∑ i', uR i' i * b i) + (∑ i, ∑ j', uC j' i * b i) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun i j' => uC j' i * b i)]
  refine ⟨x_avg, u_avg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) (Ax_avg)_i ≥ b_i.
  · intro i
    rw [hAx_avg i, le_div_iff₀ hN_pos]
    -- N * b_i ≤ ∑_k (Ax_k)_i.
    rw [← hN_card]
    have hR : ∀ i', (∑ j, A i j * xR i' j) ≥ b i := fun i' => hxR_A i' i
    have hC : ∀ j', (∑ j, A i j * xC j' j) ≥ b i := fun j' => hxC_A j' i
    have hRs : (∑ i', ∑ j, A i j * xR i' j) ≥ Fintype.card I * b i := by
      calc (∑ i', ∑ j, A i j * xR i' j) ≥ ∑ _i' : I, b i :=
             Finset.sum_le_sum (fun i' _ => hR i')
        _ = Fintype.card I * b i := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hCs : (∑ j', ∑ j, A i j * xC j' j) ≥ n * b i := by
      calc (∑ j', ∑ j, A i j * xC j' j) ≥ ∑ _j' : Fin n, b i :=
             Finset.sum_le_sum (fun j' _ => hC j')
        _ = n * b i := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  -- (2) x_avg ≥ 0.
  · intro j
    rw [hx_avg_def]
    apply div_nonneg _ hN_pos.le
    have hRs : 0 ≤ ∑ i, xR i j := Finset.sum_nonneg (fun i _ => hxR_nn i j)
    have hCs : 0 ≤ ∑ j', xC j' j := Finset.sum_nonneg (fun j' _ => hxC_nn j' j)
    linarith
  -- (3) DualFeasible u_avg.
  · refine ⟨?_, ?_⟩
    · intro i
      rw [hu_avg_def]
      apply div_nonneg _ hN_pos.le
      have hRs : 0 ≤ ∑ i', uR i' i := Finset.sum_nonneg (fun i' _ => (huR_du i').1 i)
      have hCs : 0 ≤ ∑ j', uC j' i := Finset.sum_nonneg (fun j' _ => (huC_du j').1 i)
      linarith
    · intro j
      rw [huA_avg j, div_le_iff₀ hN_pos]
      rw [← hN_card]
      have hR : ∀ i', (∑ i, uR i' i * A i j) ≤ c j := fun i' => (huR_du i').2 j
      have hC : ∀ j', (∑ i, uC j' i * A i j) ≤ c j := fun j' => (huC_du j').2 j
      have hRs : (∑ i', ∑ i, uR i' i * A i j) ≤ Fintype.card I * c j := by
        calc (∑ i', ∑ i, uR i' i * A i j) ≤ ∑ _i' : I, c j :=
               Finset.sum_le_sum (fun i' _ => hR i')
          _ = Fintype.card I * c j := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hCs : (∑ j', ∑ i, uC j' i * A i j) ≤ n * c j := by
        calc (∑ j', ∑ i, uC j' i * A i j) ≤ ∑ _j' : Fin n, c j :=
               Finset.sum_le_sum (fun j' _ => hC j')
          _ = n * c j := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith
  -- (4) ⟨c, x_avg⟩ = v.
  · rw [hcx_avg]
    have hR : ∀ i', (∑ j, c j * xR i' j) = v := fun i' => hxR_cx i'
    have hC : ∀ j', (∑ j, c j * xC j' j) = v := fun j' => hxC_cx j'
    rw [show (∑ i', ∑ j, c j * xR i' j) = Fintype.card I * v from by
      have h1 : (∑ i', ∑ j, c j * xR i' j) = ∑ _i' : I, v :=
        Finset.sum_congr rfl (fun i' _ => hR i')
      rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [show (∑ j', ∑ j, c j * xC j' j) = n * v from by
      have h1 : (∑ j', ∑ j, c j * xC j' j) = ∑ _j' : Fin n, v :=
        Finset.sum_congr rfl (fun j' _ => hC j')
      rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [show ((Fintype.card I : 𝕜) * v + n * v) = N * v from by
      rw [← hN_card]; ring]
    field_simp
  -- (5) ⟨u_avg, b⟩ = v.
  · rw [hub_avg]
    have hR : ∀ i', (∑ i, uR i' i * b i) = v := fun i' => huR_ub i'
    have hC : ∀ j', (∑ i, uC j' i * b i) = v := fun j' => huC_ub j'
    rw [show (∑ i', ∑ i, uR i' i * b i) = Fintype.card I * v from by
      have h1 : (∑ i', ∑ i, uR i' i * b i) = ∑ _i' : I, v :=
        Finset.sum_congr rfl (fun i' _ => hR i')
      rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [show (∑ j', ∑ i, uC j' i * b i) = n * v from by
      have h1 : (∑ j', ∑ i, uC j' i * b i) = ∑ _j' : Fin n, v :=
        Finset.sum_congr rfl (fun j' _ => hC j')
      rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [show ((Fintype.card I : 𝕜) * v + n * v) = N * v from by
      rw [← hN_card]; ring]
    field_simp
  -- (6) ∀ i, (Ax_avg - b)_i + u_avg_i > 0.
  · intro i
    have hAx := hAx_avg i
    have hu : u_avg i = ((∑ i', uR i' i) + (∑ j', uC j' i)) / N := hu_avg_def ▸ rfl
    rw [hAx, hu]
    rw [show ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)) / N - b i
        + ((∑ i', uR i' i) + (∑ j', uC j' i)) / N
      = ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)
         + ((∑ i', uR i' i) + (∑ j', uC j' i)) - N * b i) / N from by
      field_simp; ring]
    apply div_pos _ hN_pos
    rw [show N * b i = (Fintype.card I : 𝕜) * b i + (n : 𝕜) * b i from by
      rw [← hN_card]; ring]
    have hR_term : ∀ i', 0 ≤ ((∑ j, A i j * xR i' j) - b i + uR i' i) := fun i' => by
      linarith [hxR_A i' i, (huR_du i').1 i]
    have hC_term : ∀ j', 0 ≤ ((∑ j, A i j * xC j' j) - b i + uC j' i) := fun j' => by
      linarith [hxC_A j' i, (huC_du j').1 i]
    have hR_strict_i : 0 < ((∑ j, A i j * xR i j) - b i + uR i i) := hR_strict i
    have hR_sum_id : (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i))
        = (∑ i', ∑ j, A i j * xR i' j) + (∑ i', uR i' i) - (Fintype.card I : 𝕜) * b i := by
      rw [show (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i))
          = (∑ i', ((∑ j, A i j * xR i' j) + uR i' i - b i)) from
            Finset.sum_congr rfl (fun i' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ i', ((∑ j, A i j * xR i' j) + uR i' i))
          = (∑ i', ∑ j, A i j * xR i' j) + (∑ i', uR i' i) from
            Finset.sum_add_distrib]
      rw [show (∑ _i' : I, b i) = (Fintype.card I : 𝕜) * b i from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hC_sum_id : (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i))
        = (∑ j', ∑ j, A i j * xC j' j) + (∑ j', uC j' i) - (n : 𝕜) * b i := by
      rw [show (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i))
          = (∑ j', ((∑ j, A i j * xC j' j) + uC j' i - b i)) from
            Finset.sum_congr rfl (fun j' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ j', ((∑ j, A i j * xC j' j) + uC j' i))
          = (∑ j', ∑ j, A i j * xC j' j) + (∑ j', uC j' i) from
            Finset.sum_add_distrib]
      rw [show (∑ _j' : Fin n, b i) = (n : 𝕜) * b i from by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    have hR_sum_pos : 0 < (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i)) :=
      Finset.sum_pos' (fun i' _ => hR_term i') ⟨i, Finset.mem_univ _, hR_strict_i⟩
    have hC_sum_nn : 0 ≤ (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i)) :=
      Finset.sum_nonneg (fun j' _ => hC_term j')
    linarith [hR_sum_id, hC_sum_id]
  -- (7) ∀ j, x_avg j + (c_j - (u_avgᵀA)_j) > 0.
  · intro j
    have hxj : x_avg j = ((∑ i', xR i' j) + (∑ j'', xC j'' j)) / N := hx_avg_def ▸ rfl
    have huA := huA_avg j
    rw [hxj, huA]
    rw [show ((∑ i', xR i' j) + (∑ j'', xC j'' j)) / N
        + (c j - ((∑ i', ∑ i, uR i' i * A i j) + (∑ j'', ∑ i, uC j'' i * A i j)) / N)
      = (((∑ i', xR i' j) + (∑ j'', xC j'' j)) + N * c j
         - ((∑ i', ∑ i, uR i' i * A i j) + (∑ j'', ∑ i, uC j'' i * A i j))) / N from by
      field_simp; ring]
    apply div_pos _ hN_pos
    rw [show N * c j = (Fintype.card I : 𝕜) * c j + (n : 𝕜) * c j from by
      rw [← hN_card]; ring]
    have hR_term : ∀ i', 0 ≤ (xR i' j + (c j - ∑ i, uR i' i * A i j)) := fun i' => by
      linarith [hxR_nn i' j, (huR_du i').2 j]
    have hC_term : ∀ j'', 0 ≤ (xC j'' j + (c j - ∑ i, uC j'' i * A i j)) := fun j'' => by
      linarith [hxC_nn j'' j, (huC_du j'').2 j]
    have hC_strict_j : 0 < (xC j j + (c j - ∑ i, uC j i * A i j)) := hC_strict j
    have hR_sum_id : (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j)))
        = (∑ i', xR i' j) + (Fintype.card I : 𝕜) * c j - (∑ i', ∑ i, uR i' i * A i j) := by
      rw [show (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j)))
          = (∑ i', (xR i' j + c j - ∑ i, uR i' i * A i j)) from
            Finset.sum_congr rfl (fun i' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ i', (xR i' j + c j)) = (∑ i', xR i' j) + (∑ _i' : I, c j) from
            Finset.sum_add_distrib]
      rw [show (∑ _i' : I, c j) = (Fintype.card I : 𝕜) * c j from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hC_sum_id : (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j)))
        = (∑ j'', xC j'' j) + (n : 𝕜) * c j - (∑ j'', ∑ i, uC j'' i * A i j) := by
      rw [show (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j)))
          = (∑ j'', (xC j'' j + c j - ∑ i, uC j'' i * A i j)) from
            Finset.sum_congr rfl (fun j'' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ j'', (xC j'' j + c j)) = (∑ j'', xC j'' j) + (∑ _j'' : Fin n, c j) from
            Finset.sum_add_distrib]
      rw [show (∑ _j'' : Fin n, c j) = (n : 𝕜) * c j from by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    have hR_sum_nn : 0 ≤ (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j))) :=
      Finset.sum_nonneg (fun i' _ => hR_term i')
    have hC_sum_pos : 0 < (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j))) :=
      Finset.sum_pos' (fun j'' _ => hC_term j'') ⟨j, Finset.mem_univ _, hC_strict_j⟩
    linarith [hR_sum_id, hC_sum_id]
