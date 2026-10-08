import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugRow
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraAugRowEvalInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraAugRowEvalInrFalse
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraAugRowEvalInrTrue
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraTheoremOfAlternative
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrTrueCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrFalseCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrTrueLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrFalseLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugBInrFalse
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugBInrTrue
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearAlgebra.farkas_lemma

Topic: lp_duality   Node: 6cedc2ec10c4

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkas_lemma`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Farkas' Lemma** (objective-bound form). For a finite linear system `A x ≥ b` with `S = {x | A x ≥ b}` nonempty, the primal bound "`∀ x ∈ S, ⟨c, x⟩ ≥ d`" is equivalent to the existence of a nonneg dual certificate `u` with `uᵀA = c` and `⟨u, b⟩ ≥ d`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Farkas' Lemma** (objective-bound form). For a finite linear system `A x ≥ b` with `S = {x | A x ≥ b}` nonempty, the primal bound "`∀ x ∈ S, ⟨c, x⟩ ≥ d`" is equivalent to the existence of a nonneg dual certificate `u` with `uᵀA = c` and `⟨u, b⟩ ≥ d`. -/
theorem EconCSLib.LinearAlgebra.farkas_lemma (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (d : 𝕜)
    (hS : IsFeasible A b) :
    (∀ x : Fin n → 𝕜, (∀ i, b i ≤ ∑ j, A i j * x j) → d ≤ ∑ j, c j * x j) ↔
    (∃ u : I → 𝕜, (∀ i, 0 ≤ u i)
      ∧ (∀ j, ∑ i, u i * A i j = c j)
      ∧ d ≤ ∑ i, u i * b i) := by
  constructor
  · -- (→) primal bound implies dual certificate, via ToA on augmented system
    intro h_bound
    -- Step 1: the augmented system is infeasible.
    have h_aug_infeas : ¬ IsFeasible (farkasAugA A b c d) (farkasAugB b) := by
      rintro ⟨xt, hxt⟩
      set x : Fin n → 𝕜 := fun j => xt j.castSucc with hx_def
      set t : 𝕜 := xt (Fin.last n) with ht_def
      -- Extract the three augmented-row inequalities.
      have hAx_bt : ∀ i, b i * t ≤ ∑ j, A i j * x j := by
        intro i
        have h := hxt (Sum.inl i)
        rw [show farkasAugB b (Sum.inl i) = 0 from rfl,
            augRowEval_inl A b c d i xt] at h
        linarith
      have ht_nn : 0 ≤ t := by
        have h := hxt (Sum.inr false)
        rw [show farkasAugB b (Sum.inr false) = 0 from rfl,
            augRowEval_inr_false A b c d xt] at h
        exact h
      have hc_bound : 1 + (∑ j, c j * x j) ≤ d * t := by
        have h := hxt (Sum.inr true)
        rw [show farkasAugB b (Sum.inr true) = 1 from rfl,
            augRowEval_inr_true A b c d xt] at h
        linarith
      -- Case split on sign of t.
      rcases lt_or_eq_of_le ht_nn with ht_pos | ht_zero
      · -- t > 0: rescaling produces a feasible point with ⟨c, ·⟩ < d.
        let x' : Fin n → 𝕜 := fun j => x j / t
        have hx'_feas : ∀ i, b i ≤ ∑ j, A i j * x' j := by
          intro i
          have hAx_div : (∑ j, A i j * x' j) = (∑ j, A i j * x j) / t := by
            rw [eq_comm, Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro j _; show A i j * x j / t = A i j * (x j / t); ring
          rw [hAx_div, le_div_iff₀ ht_pos]
          linarith [hAx_bt i]
        have hx'_bnd : d ≤ ∑ j, c j * x' j := h_bound x' hx'_feas
        have hcx' : (∑ j, c j * x' j) = (∑ j, c j * x j) / t := by
          rw [eq_comm, Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro j _; show c j * x j / t = c j * (x j / t); ring
        rw [hcx'] at hx'_bnd
        -- d ≤ (∑ c j * x j) / t and 1 + (∑ c j * x j) ≤ d * t  →  contradiction.
        have h_div_le : (∑ j, c j * x j) / t ≤ d - 1 / t := by
          rw [div_le_iff₀ ht_pos]
          have : (d - 1 / t) * t = d * t - 1 := by
            field_simp
          linarith
        have h_one_div_pos : 0 < (1 : 𝕜) / t := one_div_pos.mpr ht_pos
        linarith
      · -- t = 0: recession direction contradicts the primal bound.
        have ht : t = 0 := ht_zero.symm
        have hx_rec : ∀ i, 0 ≤ ∑ j, A i j * x j := by
          intro i; have := hAx_bt i; rw [ht, mul_zero] at this; exact this
        have hcx_neg : ∑ j, c j * x j ≤ -1 := by
          have := hc_bound; rw [ht, mul_zero] at this; linarith
        obtain ⟨y, hy_orig⟩ := hS
        have hy : ∀ i, b i ≤ ∑ j, A i j * y j :=
          fun i => by simpa [rowEval] using hy_orig i
        have hcy : d ≤ ∑ j, c j * y j := h_bound y hy
        -- Mix y and x: yLam := y + λ * x, λ chosen large enough.
        let lam : 𝕜 := (∑ j, c j * y j) - d + 1
        have hlam_pos : 0 < lam := by
          show 0 < (∑ j, c j * y j) - d + 1
          linarith
        let yLam : Fin n → 𝕜 := fun j => y j + lam * x j
        have h_lin_A : ∀ i, (∑ j, A i j * yLam j)
            = (∑ j, A i j * y j) + lam * (∑ j, A i j * x j) := by
          intro i
          show (∑ j, A i j * (y j + lam * x j))
            = (∑ j, A i j * y j) + lam * (∑ j, A i j * x j)
          rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _; ring
        have h_lin_c : (∑ j, c j * yLam j)
            = (∑ j, c j * y j) + lam * (∑ j, c j * x j) := by
          show (∑ j, c j * (y j + lam * x j))
            = (∑ j, c j * y j) + lam * (∑ j, c j * x j)
          rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _; ring
        have hyLam_feas : ∀ i, b i ≤ ∑ j, A i j * yLam j := by
          intro i
          rw [h_lin_A i]
          have h1 := hy i
          have h2 : (0 : 𝕜) ≤ lam * (∑ j, A i j * x j) :=
            mul_nonneg hlam_pos.le (hx_rec i)
          linarith [h1, h2]
        have hyLam_bnd : d ≤ ∑ j, c j * yLam j := h_bound yLam hyLam_feas
        rw [h_lin_c] at hyLam_bnd
        -- Combine: d ≤ ⟨c, y⟩ + lam * ⟨c, x⟩ ≤ ⟨c, y⟩ - lam = d - 1, contradiction.
        have hcx_scaled : lam * (∑ j, c j * x j) ≤ lam * (-1) :=
          mul_le_mul_of_nonneg_left hcx_neg hlam_pos.le
        show False
        have hlam_eq : lam = (∑ j, c j * y j) - d + 1 := rfl
        linarith
    -- Step 2: apply ToA to get a Farkas certificate of the augmented system.
    have h_aug_cert : HasCertificate (farkasAugA A b c d) (farkasAugB b) :=
      (theorem_of_alternative _ _).mp h_aug_infeas
    obtain ⟨u', hu'_nn, hu'_zero, hu'_pos⟩ := h_aug_cert
    -- Read off `β > 0` from the RHS-positivity sum.
    have hu'_b_decomp : (∑ row, u' row * farkasAugB b row) = u' (Sum.inr true) := by
      rw [Fintype.sum_sum_type]
      simp [Fintype.sum_bool, farkasAugB_inl, farkasAugB_inr_false,
            farkasAugB_inr_true]
    rw [hu'_b_decomp] at hu'_pos
    set β : 𝕜 := u' (Sum.inr true) with hβ_def
    have hβ_pos : 0 < β := hu'_pos
    -- Read off uᵀA = β · c from the column conditions at j.castSucc, j : Fin n.
    have hcol_castSucc : ∀ j' : Fin n,
        (∑ i : I, u' (Sum.inl i) * A i j') = β * c j' := by
      intro j'
      have h := hu'_zero j'.castSucc
      rw [Fintype.sum_sum_type] at h
      simp only [farkasAugA_inl_castSucc, Fintype.sum_bool,
                 farkasAugA_inr_false_castSucc, farkasAugA_inr_true_castSucc,
                 mul_zero, mul_neg] at h
      -- h : (∑ i, u' (inl i) * A i j') + (u' (inr true) * (-c j') + u' (inr false) * 0) = 0
      linarith
    -- Read off ⟨u, b⟩ = α + β · d from the column condition at Fin.last n.
    have hcol_last :
        (∑ i : I, u' (Sum.inl i) * b i) = u' (Sum.inr false) + β * d := by
      have h := hu'_zero (Fin.last n)
      rw [Fintype.sum_sum_type] at h
      simp only [farkasAugA_inl_last, Fintype.sum_bool,
                 farkasAugA_inr_false_last, farkasAugA_inr_true_last] at h
      -- h : (∑ i, u' (inl i) * (-b i)) + (u' (inr true) * d + u' (inr false) * 1) = 0
      have hneg : (∑ i : I, u' (Sum.inl i) * -b i)
          = -(∑ i, u' (Sum.inl i) * b i) := by
        simp [mul_neg, Finset.sum_neg_distrib]
      rw [hneg] at h
      linarith
    -- Define u := u'(inl ·) / β and verify the three certificate conditions.
    refine ⟨fun i => u' (Sum.inl i) / β, ?_, ?_, ?_⟩
    · intro i
      exact div_nonneg (hu'_nn (Sum.inl i)) hβ_pos.le
    · intro j
      have hsum_div : (∑ i, u' (Sum.inl i) / β * A i j)
          = (∑ i, u' (Sum.inl i) * A i j) / β := by
        rw [eq_comm, Finset.sum_div]
        refine Finset.sum_congr rfl ?_
        intro i _; ring
      rw [hsum_div, hcol_castSucc j, mul_div_cancel_left₀ _ hβ_pos.ne']
    · have hsum_div : (∑ i, u' (Sum.inl i) / β * b i)
          = (∑ i, u' (Sum.inl i) * b i) / β := by
        rw [eq_comm, Finset.sum_div]
        refine Finset.sum_congr rfl ?_
        intro i _; ring
      rw [hsum_div, hcol_last, add_div, mul_div_cancel_left₀ _ hβ_pos.ne']
      have : 0 ≤ u' (Sum.inr false) / β :=
        div_nonneg (hu'_nn (Sum.inr false)) hβ_pos.le
      linarith
  · -- (←) dual certificate implies primal bound, by weighted sum.
    rintro ⟨u, hu_nn, hu_eq, hu_b⟩ x hx
    calc d ≤ ∑ i, u i * b i := hu_b
      _ ≤ ∑ i, u i * (∑ j, A i j * x j) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hx i) (hu_nn i)
      _ = ∑ j, c j * x j := by
          have step1 : (∑ i, u i * ∑ j, A i j * x j)
              = ∑ j, (∑ i, u i * A i j) * x j := by
            have h1 : (∑ i, u i * ∑ j, A i j * x j)
                = ∑ i, ∑ j, u i * (A i j * x j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
            have h2 : (∑ i, ∑ j, u i * (A i j * x j))
                = ∑ j, ∑ i, u i * (A i j * x j) := Finset.sum_comm
            have h3 : (∑ j, ∑ i, u i * (A i j * x j))
                = ∑ j, (∑ i, u i * A i j) * x j := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              ring
            rw [h1, h2, h3]
          rw [step1]
          refine Finset.sum_congr rfl ?_
          intro j _; rw [hu_eq j]
