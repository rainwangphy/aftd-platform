import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate

/-!
# EconCSLib.LinearAlgebra.feas_cert_disjoint

Topic: lp_duality   Node: 9fb1bcc649c6

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.feas_cert_disjoint`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.feas_cert_disjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem EconCSLib.LinearAlgebra.feas_cert_disjoint {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) (hcert : HasCertificate A b) : False := by
  obtain ⟨x, hx⟩ := hfeas
  obtain ⟨u, hu_nn, hu_zero, hu_pos⟩ := hcert
  -- ⟨u, b⟩ ≤ ⟨u, Ax⟩ = ⟨uᵀA, x⟩ = ⟨0, x⟩ = 0 < ⟨u, b⟩.
  have hweighted : ∑ i, u i * b i ≤ ∑ i, u i * rowEval A i x := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hx i) (hu_nn i)
  have hzero : ∑ i, u i * rowEval A i x = 0 := by
    have h1 : ∑ i, u i * rowEval A i x = ∑ i, ∑ j, u i * (A i j * x j) := by
      simp only [rowEval, Finset.mul_sum]
    have h2 : (∑ i, ∑ j, u i * (A i j * x j))
        = ∑ j, ∑ i, u i * A i j * x j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h3 : (∑ j, ∑ i, u i * A i j * x j)
        = ∑ j, (∑ i, u i * A i j) * x j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    rw [h1, h2, h3]
    apply Finset.sum_eq_zero
    intro j _
    rw [hu_zero j, zero_mul]
  linarith
