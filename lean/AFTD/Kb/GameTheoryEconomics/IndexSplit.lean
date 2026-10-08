import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.PrefixSum
import AFTD.Kb.GameTheoryEconomics.IndexSplitExistence

/-!
# index_split

Topic: general_equilibrium   Node: 07b93d707c26

Provenance: formalization of a published result. Source: EconCSLib, `index_split`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Split a flat index `k` into its block/index pair `(i, j)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Split a flat index `k` into its block/index pair `(i, j)`. -/
noncomputable def index_split (k : Fin (total_card card)) : Σ i, Fin (card i) :=
  Classical.choose (index_split_existence card k)
