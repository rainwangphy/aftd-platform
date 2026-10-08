import AFTD.Prelude

/-!
# stdSimplex.mix

Topic: lp_duality   Node: a5adf930387c

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination of two simplex points: `mix α hα₀ hα₁ x y = α·x + (1-α)·y`. This is the basic vocabulary for compound lotteries and for any inductive argument that interpolates between two mixed strategies (Loomis, Sion, fictitious play). The hypotheses are passed as plain `(α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)` rather than via a unit-interval subtype to match Mathlib idioms and to keep call sites lightweight.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Convex combination of two simplex points: `mix α hα₀ hα₁ x y = α·x + (1-α)·y`. This is the basic vocabulary for compound lotteries and for any inductive argument that interpolates between two mixed strategies (Loomis, Sion, fictitious play). The hypotheses are passed as plain `(α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)` rather than via a unit-interval subtype to match Mathlib idioms and to keep call sites lightweight. -/
def stdSimplex.mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) : stdSimplex 𝕜 I where
  val i := α * x.val i + (1 - α) * y.val i
  property := by
    refine ⟨fun i => ?_, ?_⟩
    · have hx := x.property.1 i
      have hy := y.property.1 i
      have hα' : 0 ≤ 1 - α := by linarith
      have h₁ : 0 ≤ α * x.val i := mul_nonneg hα₀ hx
      have h₂ : 0 ≤ (1 - α) * y.val i := mul_nonneg hα' hy
      linarith
    · have hxsum := x.property.2
      have hysum := y.property.2
      have : (∑ i, (α * x.val i + (1 - α) * y.val i))
          = α * (∑ i, x.val i) + (1 - α) * (∑ i, y.val i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [this, hxsum, hysum]; ring
