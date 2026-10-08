import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.IndexSplit
import AFTD.Kb.GameTheoryEconomics.PrefixSum
import AFTD.Kb.GameTheoryEconomics.IndexSplitSpec

/-!
# index_combine_split_inverse

Topic: general_equilibrium   Node: d84363740449

Provenance: formalization of a published result. Source: EconCSLib, `index_combine_split_inverse`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`index_combine` is a left inverse to `index_split`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `index_combine` is a left inverse to `index_split`. -/
lemma index_combine_split_inverse (k : Fin (total_card card)) : index_combine card (index_split card k) = k := by
  classical
  have hspec := index_split_spec card k
  apply Fin.ext
  simp [index_combine, hspec.2.2, Nat.add_sub_of_le hspec.1]
