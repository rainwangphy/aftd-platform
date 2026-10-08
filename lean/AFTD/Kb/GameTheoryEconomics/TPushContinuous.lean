import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.DeficitContinuous
import AFTD.Kb.GameTheoryEconomics.DeficitNonneg

/-!
# tPush_continuous

Topic: general_equilibrium   Node: 7c638422478f

Provenance: formalization of a published result. Source: EconCSLib, `tPush_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuity of `tPush card`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `tPush card`. -/
lemma tPush_continuous : Continuous (tPush card) := by
  have h_denom_cont : Continuous (fun x => (1 : ℝ) + deficit card x) :=
    continuous_const.add (deficit_continuous card)
  have h_denom_ne : ∀ x, (1 : ℝ) + deficit card x ≠ 0 := fun x =>
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x))
  exact Continuous.div (deficit_continuous card) h_denom_cont h_denom_ne
