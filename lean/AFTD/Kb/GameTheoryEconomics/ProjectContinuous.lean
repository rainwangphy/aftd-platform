import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.ProductSimplices
import AFTD.Kb.GameTheoryEconomics.ProjectToProduct
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.PushTowardsZContinuous
import AFTD.Kb.GameTheoryEconomics.BlockSumPushTowardsZPos

/-!
# project_continuous

Topic: general_equilibrium   Node: fe394f4013eb

Provenance: formalization of a published result. Source: EconCSLib, `project_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuity of `project_to_product`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `project_to_product`. -/
lemma project_continuous : Continuous (project_to_product card) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let k : Fin (total_card card) := index_combine card ⟨i, j⟩
  have h_num_cont : Continuous (fun x : BigSimplex card => (pushTowardsZ card x).1 k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_cont : Continuous (fun x : BigSimplex card =>
      blockSum card i (pushTowardsZ card x)) := by
    change Continuous (fun x : BigSimplex card =>
      ∑ j : Fin (card i), (pushTowardsZ card x).1 (index_combine card ⟨i, j⟩))
    apply continuous_finset_sum
    intro j _
    exact (continuous_apply (index_combine card ⟨i, j⟩)).comp
      (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_ne : ∀ x : BigSimplex card, blockSum card i (pushTowardsZ card x) ≠ 0 :=
    fun x => ne_of_gt (blockSum_pushTowardsZ_pos card i x)
  have h_div : Continuous (fun x : BigSimplex card =>
      (pushTowardsZ card x).1 k / blockSum card i (pushTowardsZ card x)) :=
    Continuous.div h_num_cont h_denom_cont h_denom_ne
  simpa [project_to_product, blockSum] using h_div
