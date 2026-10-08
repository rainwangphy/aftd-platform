import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.TotalCard

/-!
# blockWeight_pos

Topic: general_equilibrium   Node: 0e5c7727952d

Provenance: formalization of a published result. Source: EconCSLib, `blockWeight_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

blockWeight_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
omit [DecidableEq I] [LinearOrder I] in
lemma blockWeight_pos (i : I) : 0 < blockWeight card i := by
  unfold blockWeight
  have htc : 0 < (total_card card : ℝ) := by norm_cast; exact PNat.pos (total_card card)
  have hci : 0 < (card i : ℝ) := by norm_cast; exact PNat.pos (card i)
  exact div_pos hci htc
