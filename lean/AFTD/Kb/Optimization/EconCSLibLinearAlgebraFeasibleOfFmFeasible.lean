import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraReducedPairIneq
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.feasible_of_fm_feasible

Topic: lp_duality   Node: 7f2f4fb6638a

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.feasible_of_fm_feasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.feasible_of_fm_feasible
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.feasible_of_fm_feasible (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hred : IsFeasible (fmA A) (fmB A b)) : IsFeasible A b := by
  obtain ⟨x', hx'⟩ := hred
  classical
  -- Per-row lower/upper bounds (defined on subtypes).
  let L : PosRows A → 𝕜 := fun p =>
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
  let U : NegRows A → 𝕜 := fun q =>
    (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n)
  -- Choose x_last by case-split on emptiness of PosRows / NegRows.
  let x_last : 𝕜 :=
    if hPos : (Finset.univ : Finset (PosRows A)).Nonempty then
      Finset.univ.sup' hPos L
    else if hNeg : (Finset.univ : Finset (NegRows A)).Nonempty then
      Finset.univ.inf' hNeg U
    else (0 : 𝕜)
  refine ⟨Fin.snoc x' x_last, ?_⟩
  intro i
  -- Decompose original row evaluation: first n + last entry.
  have hsplit : rowEval A i (Fin.snoc x' x_last)
      = (∑ j : Fin n, A i j.castSucc * x' j)
        + A i (Fin.last n) * x_last := by
    rw [rowEval_def, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rcases lt_trichotomy (A i (Fin.last n)) 0 with hlt | heq | hgt
  · -- Negative last-column coefficient: i ∈ NegRows.
    let hiN : NegRows A := ⟨i, hlt⟩
    have hUbound : x_last ≤ U hiN := by
      by_cases hPos : (Finset.univ : Finset (PosRows A)).Nonempty
      · -- x_last = sup' L; need sup' L ≤ U(hiN), i.e., ∀ p, L p ≤ U hiN.
        change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dif_pos hPos]
        apply Finset.sup'_le
        intro p _
        exact reduced_pair_ineq hx' p hiN
      · -- x_last = inf' U (NegRows nonempty since hiN exists).
        have hNeg : (Finset.univ : Finset (NegRows A)).Nonempty :=
          ⟨hiN, Finset.mem_univ _⟩
        change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dif_neg hPos, dif_pos hNeg]
        exact Finset.inf'_le _ (Finset.mem_univ hiN)
    have hUval : A i (Fin.last n) * U hiN
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      show A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_lt hlt
      field_simp
    have hmul : A i (Fin.last n) * U hiN ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonpos_left hUbound hlt.le
    rw [hsplit]
    linarith
  · -- Zero last-column coefficient: i ∈ ZeroRows.
    let hiZ : ZeroRows A := ⟨i, heq⟩
    have h := hx' (Sum.inl hiZ)
    simp only [fmB_inl, rowEval_def, fmA_inl] at h
    rw [hsplit, heq, zero_mul, add_zero]
    exact h
  · -- Positive last-column coefficient: i ∈ PosRows.
    let hiP : PosRows A := ⟨i, hgt⟩
    have hPos : (Finset.univ : Finset (PosRows A)).Nonempty :=
      ⟨hiP, Finset.mem_univ _⟩
    have hLbound : L hiP ≤ x_last := by
      change L hiP ≤ (if h : _ then Finset.univ.sup' h L
                       else if h' : _ then Finset.univ.inf' h' U else 0)
      rw [dif_pos hPos]
      exact Finset.le_sup' _ (Finset.mem_univ hiP)
    have hLval : A i (Fin.last n) * L hiP
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      show A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_gt hgt
      field_simp
    have hmul : A i (Fin.last n) * L hiP ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonneg_left hLbound hgt.le
    rw [hsplit]
    linarith
