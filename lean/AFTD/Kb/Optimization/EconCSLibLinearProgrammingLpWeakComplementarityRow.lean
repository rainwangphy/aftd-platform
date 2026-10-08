import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible

/-!
# EconCSLib.LinearProgramming.lp_weak_complementarity_row

Topic: lp_duality   Node: ed800e03d537

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.lp_weak_complementarity_row`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Weak complementary slackness**, row form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Weak complementary slackness**, row form. -/
theorem EconCSLib.LinearProgramming.lp_weak_complementarity_row
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    {x : Fin n → 𝕜} (hxA : ∀ i, b i ≤ ∑ j, A i j * x j) (hxnn : ∀ j, 0 ≤ x j)
    {u : I → 𝕜} (hu_du : DualFeasible A c u)
    (h_match : ∑ j, c j * x j = ∑ i, u i * b i) :
    ∀ i, (∑ j, A i j * x j - b i) * u i = 0 := by
  obtain ⟨hu_nn, hu_le⟩ := hu_du
  -- Sum identity: ∑ u_i * (A x - b)_i + ∑ x_j * (c - uᵀA)_j = ⟨c, x⟩ - ⟨u, b⟩ = 0.
  have hsum1 : (∑ i, u i * (∑ j, A i j * x j - b i))
             + (∑ j, x j * (c j - ∑ i, u i * A i j)) = 0 := by
    have h1 : (∑ i, u i * (∑ j, A i j * x j - b i))
            = (∑ i, ∑ j, u i * (A i j * x j)) - ∑ i, u i * b i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_sub, Finset.mul_sum]
    have h2 : (∑ j, x j * (c j - ∑ i, u i * A i j))
            = (∑ j, c j * x j) - (∑ j, x j * ∑ i, u i * A i j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_sub, mul_comm (x j) (c j)]
    have hcross : (∑ i, ∑ j, u i * (A i j * x j))
                = (∑ j, x j * ∑ i, u i * A i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [h1, h2, hcross]
    linarith [h_match]
  -- Each term in hsum1 is ≥ 0 (nonneg variable times nonneg slack), so each is 0.
  have hterm_row : ∀ i ∈ Finset.univ, 0 ≤ u i * (∑ j, A i j * x j - b i) := by
    intro i _
    exact mul_nonneg (hu_nn i) (by linarith [hxA i])
  have hterm_col : ∀ j ∈ Finset.univ, 0 ≤ x j * (c j - ∑ i, u i * A i j) := by
    intro j _
    exact mul_nonneg (hxnn j) (by linarith [hu_le j])
  have hsum_row_nn : 0 ≤ ∑ i, u i * (∑ j, A i j * x j - b i) :=
    Finset.sum_nonneg hterm_row
  have hsum_col_nn : 0 ≤ ∑ j, x j * (c j - ∑ i, u i * A i j) :=
    Finset.sum_nonneg hterm_col
  have hsum_row_zero : ∑ i, u i * (∑ j, A i j * x j - b i) = 0 := by linarith
  -- Each individual term is 0.
  intro i
  have hindiv : u i * (∑ j, A i j * x j - b i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_row).mp hsum_row_zero i (Finset.mem_univ i)
  rw [mul_comm] at hindiv
  exact hindiv
