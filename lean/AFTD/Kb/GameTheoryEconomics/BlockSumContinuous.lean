import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.IndexCombine

/-!
# blockSum_continuous

Topic: general_equilibrium   Node: 25bfa2a030f3

Provenance: formalization of a published result. Source: EconCSLib, `blockSum_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuity of `blockSum card i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `blockSum card i`. -/
lemma blockSum_continuous (i : I) : Continuous (blockSum card i) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ j : Fin (card i), x.1 (index_combine card ⟨i, j⟩))
  apply continuous_finset_sum
  intro j _
  exact (continuous_apply _).comp continuous_subtype_val
