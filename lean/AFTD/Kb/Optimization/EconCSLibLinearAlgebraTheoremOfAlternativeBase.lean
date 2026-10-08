import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFeasCertDisjoint
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearAlgebra.theorem_of_alternative_base

Topic: lp_duality   Node: d442f63f9121

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.theorem_of_alternative_base`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.theorem_of_alternative_base
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.theorem_of_alternative_base
    {I : Type*} [Fintype I] [DecidableEq I] (A : I → Fin 0 → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasCertificate A b := by
  classical
  refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
  intro hinf
  -- `IsFeasible ↔ ∀ i, b i ≤ 0`; the negation provides an index with `0 < b i`.
  have h_pick : ∃ i : I, 0 < b i := by
    by_contra hall
    push Not at hall
    apply hinf
    refine ⟨fun j : Fin 0 => Fin.elim0 j, fun i => ?_⟩
    have h_row_zero : rowEval A i (fun j : Fin 0 => Fin.elim0 j) = 0 := by
      unfold rowEval
      apply Finset.sum_eq_zero
      intro j _
      exact Fin.elim0 j
    rw [h_row_zero]
    exact hall i
  obtain ⟨i₀, hi₀⟩ := h_pick
  refine ⟨fun i => if i₀ = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i
    show 0 ≤ if i₀ = i then (1 : 𝕜) else 0
    split_ifs <;> norm_num
  · intro j; exact Fin.elim0 j
  · -- ∑ i, (if i₀ = i then 1 else 0) * b i = b i₀ > 0
    show 0 < ∑ i, (if i₀ = i then (1 : 𝕜) else 0) * b i
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
    exact hi₀
