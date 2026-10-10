import AFTD.Prelude

/-!
# Cosmology.FLRW.FriedmannEquation.sq_deSitterRate

Topic: cosmology   Node: 0f85445f1bc7

Provenance: formalization of a published result. Source: Physlib, `Cosmology.FLRW.FriedmannEquation.sq_deSitterRate`. Lean proof by Philippe Kevorkian, Jinzheng Li, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Solutions.lean (Copyright (c) 2026 Jinzheng Li. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`σ² (√(Λ/3))² c² = Λ c² / 3` for `σ = ±1` and `0 ≤ Λ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
/-- `σ² (√(Λ/3))² c² = Λ c² / 3` for `σ = ±1` and `0 ≤ Λ`. -/
lemma Cosmology.FLRW.FriedmannEquation.sq_deSitterRate {σ Λ c : ℝ} (hΛ : 0 ≤ Λ) (hσ : σ = 1 ∨ σ = -1) :
    (σ * √(Λ / 3) * c) ^ 2 = Λ * c ^ 2 / 3 := by
  have hs : √(Λ / 3) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  rcases hσ with rfl | rfl <;> linear_combination c ^ 2 * hs
