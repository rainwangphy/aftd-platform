import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProductSimplices
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.EmbedFromProduct
import AFTD.Kb.GameTheoryEconomics.IndexSplit

/-!
# embed_continuous

Topic: general_equilibrium   Node: b4bf5f309050

Provenance: formalization of a published result. Source: EconCSLib, `embed_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuity of `embed_from_product`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `embed_from_product`. -/
lemma embed_continuous : Continuous (embed_from_product card) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  let p := index_split card k
  apply Continuous.div
  · apply Continuous.mul
    · have h1 : (fun y : ProductSimplices card => (y p.1).1 p.2) =
                (fun z => z p.2) ∘ (fun w => w.1) ∘ (fun y => y p.1) := by
        rfl
      rw [h1]
      apply Continuous.comp
      · apply continuous_apply
      · apply Continuous.comp
        · apply continuous_subtype_val
        · apply continuous_apply
    · exact continuous_const
  · exact continuous_const
  · intro y
    simp only [total_card]
    norm_cast
    apply ne_of_gt
    apply Finset.sum_pos
    · intro i _
      exact PNat.pos (card i)
    · exact Finset.univ_nonempty
