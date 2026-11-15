import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasBivaluedEfxSubMmsInstance
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# op_1719_bivalued_efx_sub_mms_two_agents_two_ratio

Topic: fair_division   Node: 3b4929baafa6

Provenance: original. Related work: arXiv:2611.15582

For two agents and item values in {1, 2}, there exists an additive instance with a complete EFX allocation in which some agent obtains strictly less than her 1-out-of-2 maximin share, so has_bivalued_efx_sub_mms_instance 2 2 2 holds.
-/

def op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u : Fin 2 → Fin 4 → ℝ :=
  fun _ g => if g.val < 2 then 1 else 2

def op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_σ : Fin 4 → Fin 2 :=
  fun g => if g.val < 2 then 0 else 1

def op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P : Fin 4 → Fin 2 :=
  fun g => ⟨g.val % 2, by omega⟩

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b0 :
    bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_σ 0 = {0, 1} := by decide

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b1 :
    bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_σ 1 = {2, 3} := by decide

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_p0 :
    bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P 0 = {0, 2} := by decide

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_p1 :
    bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P 1 = {1, 3} := by decide

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_01 (i : Fin 2) :
    additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i) {0, 1} = 2 := by
  dsimp [additive_valuation, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]
  have : (0 : Fin 4) ≠ 1 := by decide
  rw [Finset.sum_pair this]
  norm_num

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_23 (i : Fin 2) :
    additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i) {2, 3} = 4 := by
  dsimp [additive_valuation, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]
  have : (2 : Fin 4) ≠ 3 := by decide
  rw [Finset.sum_pair this]
  norm_num

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_02 (i : Fin 2) :
    additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i) {0, 2} = 3 := by
  dsimp [additive_valuation, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]
  have : (0 : Fin 4) ≠ 2 := by decide
  rw [Finset.sum_pair this]
  norm_num

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_13 (i : Fin 2) :
    additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i) {1, 3} = 3 := by
  dsimp [additive_valuation, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]
  have : (1 : Fin 4) ≠ 3 := by decide
  rw [Finset.sum_pair this]
  norm_num

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_singleton (i : Fin 2) (g : Fin 4) :
    additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i) {g} =
      op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u i g := by
  dsimp [additive_valuation]
  rw [Finset.sum_singleton]

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by omega
lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin4_cases (g : Fin 4) :
    g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_efx :
    is_efx_goods op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u
      op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_σ := by
  intro i j hij g hg
  rcases op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin2_cases i with rfl | rfl <;>
    rcases op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin2_cases j with rfl | rfl
  · contradiction
  · rw [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b0,
        op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b1] at *
    rcases op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin4_cases g with rfl | rfl | rfl | rfl
    · exfalso; revert hg; decide
    · exfalso; revert hg; decide
    · have : ({2, 3} : Finset (Fin 4)).erase 2 = {3} := by decide
      rw [this, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_singleton,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_01]
      dsimp [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]; norm_num
    · have : ({2, 3} : Finset (Fin 4)).erase 3 = {2} := by decide
      rw [this, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_singleton,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_01]
      dsimp [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]; norm_num
  · rw [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b0,
        op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b1] at *
    rcases op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin4_cases g with rfl | rfl | rfl | rfl
    · have : ({0, 1} : Finset (Fin 4)).erase 0 = {1} := by decide
      rw [this, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_singleton,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_23]
      dsimp [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]; norm_num
    · have : ({0, 1} : Finset (Fin 4)).erase 1 = {0} := by decide
      rw [this, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_singleton,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_23]
      dsimp [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]; norm_num
    · exfalso; revert hg; decide
    · exfalso; revert hg; decide
  · contradiction

lemma op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_mms_bound :
    3 ≤ maximin_share (additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u 0)) 2 := by
  dsimp [maximin_share]
  have h1 : 3 ≤ ⨅ k : Fin 2, additive_valuation
      (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u 0)
      (bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P k) := by
    apply le_ciInf
    intro k
    rcases op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_fin2_cases k with rfl | rfl
    · rw [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_p0,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_02]
    · rw [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_p1,
          op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_13]
  have h2 : (⨅ k : Fin 2, additive_valuation
        (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u 0)
        (bundle_of op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P k)) ≤
      ⨆ P : Fin 4 → Fin 2, ⨅ k, additive_valuation
        (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u 0)
        (bundle_of P k) := by
    have hb : BddAbove (Set.range (fun P : Fin 4 → Fin 2 =>
        ⨅ k, additive_valuation (op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u 0) (bundle_of P k))) :=
      Finite.bddAbove_range _
    exact le_ciSup hb op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_P
  exact le_trans h1 h2

/-- For two agents and ratio R = 2, there exists a complete EFX allocation where some agent receives strictly less than her 1-out-of-2 maximin share. -/
theorem op_1719_bivalued_efx_sub_mms_two_agents_two_ratio :
    has_bivalued_efx_sub_mms_instance 2 2 2 := by
  dsimp [has_bivalued_efx_sub_mms_instance]
  refine ⟨4, op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u,
    op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_σ, 0, ?_,
    op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_efx, ?_⟩
  · intro j g
    dsimp [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_u]
    split_ifs
    · left; rfl
    · right; rfl
  · rw [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_b0,
        op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_sum_01]
    linarith [op_1719_bivalued_efx_sub_mms_two_agents_two_ratio_mms_bound]
