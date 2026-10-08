import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.IndexSplit
import AFTD.Kb.GameTheoryEconomics.PrefixSum
import AFTD.Kb.GameTheoryEconomics.IndexSplitExistence

/-!
# index_split_spec

Topic: general_equilibrium   Node: 779a555ec1e9

Provenance: formalization of a published result. Source: EconCSLib, `index_split_spec`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Specification of `index_split`: bounds and value relation for `(i, j)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Specification of `index_split`: bounds and value relation for `(i, j)`. -/
lemma index_split_spec (k : Fin (total_card card)) :
  let p := index_split card k
  prefix_sum card p.1 ≤ k.val ∧ k.val < prefix_sum card p.1 + (card p.1 : ℕ) ∧
  p.2.val = k.val - prefix_sum card p.1 :=
  Classical.choose_spec (index_split_existence card k)
