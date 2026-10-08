import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProductSimplices

/-!
# uniformProduct

Topic: general_equilibrium   Node: e72b02879703

Provenance: formalization of a published result. Source: EconCSLib, `uniformProduct`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The uniform point in each block simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The uniform point in each block simplex. -/
noncomputable def uniformProduct : ProductSimplices card :=
  fun i =>
    (⟨fun _ => (1 : ℝ) / (card i : ℝ), by
      simp only [stdSimplex, Set.mem_setOf_eq]
      constructor
      · intro _; apply div_nonneg; norm_num; positivity
      · simp [Finset.sum_const]
    ⟩ : stdSimplex ℝ (Fin (card i)))
