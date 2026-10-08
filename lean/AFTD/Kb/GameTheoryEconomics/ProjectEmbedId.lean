import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProductSimplices
import AFTD.Kb.GameTheoryEconomics.ProjectToProduct
import AFTD.Kb.GameTheoryEconomics.EmbedFromProduct
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.IndexSplit
import AFTD.Kb.GameTheoryEconomics.IndexSplitCombineInverse
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.ZUniform

/-!
# project_embed_id

Topic: general_equilibrium   Node: 981ac1271ff1

Provenance: formalization of a published result. Source: EconCSLib, `project_embed_id`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`project_to_product ∘ embed_from_product = id`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `project_to_product ∘ embed_from_product = id`. -/
lemma project_embed_id (y : ProductSimplices card) :
  project_to_product card (embed_from_product card y) = y := by
  classical
  have h_blockSum : ∀ i, blockSum card i (embed_from_product card y) = blockWeight card i := by
    intro i
    have :
        blockSum card i (embed_from_product card y) =
          (((∑ j : Fin (card i), (y i).1 j) * (card i : ℝ)) / (total_card card : ℝ)) := by
      classical
      have hsum :
          (∑ j : Fin (card i), (embed_from_product card y).1 (index_combine card ⟨i, j⟩)) =
            (∑ j : Fin (card i), (y i).1 j * (card i : ℝ) / (total_card card : ℝ)) := by
        refine Finset.sum_congr rfl ?_;
        intro j _
        simpa [embed_from_product] using
          congrArg
            (fun p : Σ i, Fin (card i) =>
              (y p.1).1 p.2 * (card p.1 : ℝ) / (total_card card : ℝ))
            (index_split_combine_inverse card ⟨i, j⟩)
      simpa [blockSum, Finset.sum_div, Finset.sum_mul] using hsum
    simpa [blockWeight, (y i).2.2, one_mul] using this
  have h_deficit_zero : deficit card (embed_from_product card y) = 0 := by
    simp [deficit, h_blockSum]
  have h_tPush_zero : tPush card (embed_from_product card y) = 0 := by
    simp [tPush, h_deficit_zero]
  have h_push_id : pushTowardsZ card (embed_from_product card y) = embed_from_product card y := by
    apply Subtype.ext
    funext k
    simp [pushTowardsZ, h_tPush_zero]
  funext i
  apply Subtype.ext
  funext j
  have h_denom :
      blockSum card i (pushTowardsZ card (embed_from_product card y)) = blockWeight card i := by
    simpa [h_push_id] using h_blockSum i
  have h_bw_pos : 0 < blockWeight card i := by
    unfold blockWeight
    have htc : 0 < (total_card card : ℝ) := by
      norm_cast; exact PNat.pos (total_card card)
    have hci : 0 < (card i : ℝ) := by
      norm_cast; exact PNat.pos (card i)
    exact div_pos hci htc
  have h_norm_eq_div :
      ((project_to_product card (embed_from_product card y)) i).1 j =
        ((embed_from_product card y).1 (index_combine card ⟨i, j⟩)) / (blockWeight card i) := by
    simp [project_to_product, h_push_id]
    rw [h_blockSum i]
  have h_div_cancel :
      ((embed_from_product card y).1 (index_combine card ⟨i, j⟩)) / (blockWeight card i) =
        (y i).1 j := by
    have hnum : (embed_from_product card y).1 (index_combine card ⟨i, j⟩) =
        (y i).1 j * (card i : ℝ) / (total_card card : ℝ) := by
      simpa [embed_from_product] using
        congrArg
          (fun p : Σ i, Fin (card i) =>
            (y p.1).1 p.2 * (card p.1 : ℝ) / (total_card card : ℝ))
          (index_split_combine_inverse card ⟨i, j⟩)
    have hbw_ne : blockWeight card i ≠ 0 := ne_of_gt h_bw_pos
    have htc : (total_card card : ℝ) ≠ 0 := by
      have : 0 < (total_card card : ℝ) := by
        norm_cast; exact PNat.pos (total_card card)
      exact ne_of_gt this
    have hci : (card i : ℝ) ≠ 0 := by
      have : 0 < (card i : ℝ) := by
        norm_cast; exact PNat.pos (card i)
      exact ne_of_gt this
    have :
        ((y i).1 j * (card i : ℝ) / (total_card card : ℝ)) /
            ((card i : ℝ) / (total_card card : ℝ)) =
          (y i).1 j := by
      field_simp [hci, htc]
    simpa [hnum, blockWeight] using this
  simpa [h_norm_eq_div] using h_div_cancel
