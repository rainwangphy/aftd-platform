import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum

/-!
# wsum_pos

Topic: lp_duality   Node: 4b385cf1fd00

Provenance: formalization of a published result. Source: EconCSLib, `wsum_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum of strictly-positive values is strictly positive. Some coordinate `a` of any simplex point is strictly positive (since `∑ x = 1`), and the corresponding `x_a · f a` summand is strictly positive while every other summand is non-negative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum of strictly-positive values is strictly positive. Some coordinate `a` of any simplex point is strictly positive (since `∑ x = 1`), and the corresponding `x_a · f a` summand is strictly positive while every other summand is non-negative. -/
theorem wsum_pos (x : stdSimplex 𝕜 I) {f : I → 𝕜}
    (hf : ∀ i, 0 < f i) : 0 < wsum x f := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, 0 < x.val a := by
    by_contra hAll
    push_neg at hAll
    have hzero : ∀ i, x.val i = 0 :=
      fun i => le_antisymm (hAll i) (x.property.1 i)
    have hsum_zero : (∑ i, x.val i) = 0 := by simp_rw [hzero]; simp
    exact zero_ne_one (hsum_zero.symm.trans x.property.2)
  change 0 < ∑ b, x.val b * f b
  have hle : ∀ b ∈ (Finset.univ : Finset I), (0 : 𝕜) ≤ x.val b * f b :=
    fun b _ => mul_nonneg (x.property.1 b) (hf b).le
  have hpos : ∃ b ∈ (Finset.univ : Finset I), (0 : 𝕜) < x.val b * f b :=
    ⟨a, Finset.mem_univ _, mul_pos ha (hf a)⟩
  calc (0 : 𝕜)
      = ∑ _ : I, (0 : 𝕜) := by simp
    _ < ∑ b, x.val b * f b := Finset.sum_lt_sum hle hpos
