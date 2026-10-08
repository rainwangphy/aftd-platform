import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProductSimplices
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.IndexSplit
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.IndexCombineSplitInverse
import AFTD.Kb.GameTheoryEconomics.IndexSplitCombineInverse

/-!
# embed_from_product

Topic: general_equilibrium   Node: 29c5305b0ef4

Provenance: formalization of a published result. Source: EconCSLib, `embed_from_product`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embedding of the product of simplices into the big simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Embedding of the product of simplices into the big simplex. -/
noncomputable def embed_from_product (y : ProductSimplices card) : BigSimplex card :=
  ⟨fun k =>
    let p := index_split card k
    (y p.1).1 p.2 * (card p.1 : ℝ) / (total_card card : ℝ), by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro k
      let p := index_split card k
      have h_denom_pos : 0 < (total_card card : ℝ) := by
        norm_cast
        exact PNat.pos (total_card card)
      have h_num_nonneg : 0 ≤ (y p.1).1 p.2 * (card p.1 : ℝ) :=
        mul_nonneg ((y p.1).2.1 p.2) (by positivity)
      exact div_nonneg h_num_nonneg (le_of_lt h_denom_pos)
    · rw [← Finset.sum_div]
      have h_numerator : (∑ k, (y (index_split card k).1).1 (index_split card k).2 * (card (index_split card k).1 : ℝ)) = ↑(total_card card) := by
        have : (∑ k, (y (index_split card k).1).1 (index_split card k).2 * (card (index_split card k).1 : ℝ)) =
               (∑ i, ∑ j : Fin (card i), (y i).1 j * (card i : ℝ)) := by
          let f (p : Σ i, Fin (card i)) := (y p.1).1 p.2 * (card p.1 : ℝ)
          change
            (∑ k ∈ (Finset.univ : Finset (Fin (total_card card))), f (index_split card k)) =
            (∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset (Fin (card i))), f ⟨i, j⟩)
          rw [← Finset.sum_sigma (s := (Finset.univ : Finset I)) (t := fun i => (Finset.univ : Finset (Fin (card i))))]
          apply Finset.sum_bij (fun k _ => index_split card k)
          · intro; simp
          · intro a₁ _ a₂ _ h
            rw [← index_combine_split_inverse card a₁, ← index_combine_split_inverse card a₂, h]
          · intro k _
            use index_combine card k
            exact ⟨Finset.mem_univ _, index_split_combine_inverse card k⟩
          · intro i j; rfl
        rw [this]
        simp_rw [← Finset.sum_mul, (y _).2.2, one_mul]
        rw [← Nat.cast_sum]
        simp [total_card]
      rw [h_numerator]
      field_simp⟩
