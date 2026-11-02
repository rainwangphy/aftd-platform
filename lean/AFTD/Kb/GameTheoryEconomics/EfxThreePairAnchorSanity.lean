import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreePairAnchorValues
import AFTD.Kb.GameTheoryEconomics.EfxThreePairAnchorStart
import AFTD.Kb.GameTheoryEconomics.EfxThreePairAnchorWitness
import AFTD.Kb.GameTheoryEconomics.EfxPartialNat
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairSanity

/-!
# efx_three_pair_anchor_sanity

Topic: fair_division   Node: e446748f6bd0

Provenance: helper lemma. Common-anchor lift of the OP-7 all-source three-split barrier; experiment 11720 and an unproved anchor-count projection.

The starting allocation is envy-free with r+2 goods per bundle and one charity good; the lifted complete witness is EFX.
-/

open Finset

def efx_three_pair_anchor_sanity_equiv_prod (r : ℕ) : Fin r × Fin 4 ≃ Fin (4 * r) :=
  (finProdFinEquiv (m := r) (n := 4)).trans (finCongr (mul_comm r 4))

lemma efx_three_pair_anchor_sanity_equiv_prod_mod (r : ℕ) (x : Fin r × Fin 4) :
    (⟨(efx_three_pair_anchor_sanity_equiv_prod r x).val % 4, by omega⟩ : Fin 4) = x.2 := by
  ext
  dsimp [efx_three_pair_anchor_sanity_equiv_prod, finProdFinEquiv]
  simp

lemma efx_three_pair_anchor_sanity_sum_mod_four (r : ℕ) (j : Fin 4) :
    (∑ g : Fin (4 * r), (if (⟨g.val % 4, by omega⟩ : Fin 4) = j then (100 : ℕ) else 0)) = 100 * r := by
  rw [← (efx_three_pair_anchor_sanity_equiv_prod r).sum_comp]
  simp_rw [efx_three_pair_anchor_sanity_equiv_prod_mod]
  rw [Fintype.sum_prod_type]
  simp
  ring

lemma efx_three_pair_anchor_sanity_start_natAdd_eq (r : ℕ) (j : Fin 4) (x : Fin (4 * r)) :
    (efx_three_pair_anchor_start r (Fin.natAdd 9 x) = j.castSucc) ↔ ((⟨x.val % 4, by omega⟩ : Fin 4) = j) := by
  unfold efx_three_pair_anchor_start
  have hge : ¬ ((Fin.natAdd 9 x : ℕ) < 9) := by simp
  rw [dif_neg hge]
  rw [Fin.ext_iff, Fin.ext_iff]
  simp [Fin.natAdd]

lemma efx_three_pair_anchor_sanity_start_natAdd_val (r : ℕ) (i : Fin 4) (x : Fin (4 * r)) :
    efx_three_pair_anchor_values r i (Fin.natAdd 9 x) = 100 := by
  unfold efx_three_pair_anchor_values
  have hge : ¬ ((Fin.natAdd 9 x : ℕ) < 9) := by simp
  rw [dif_neg hge]

lemma efx_three_pair_anchor_sanity_witness_natAdd_eq (r : ℕ) (j : Fin 4) (x : Fin (4 * r)) :
    (efx_three_pair_anchor_witness r (Fin.natAdd 9 x) = j) ↔ ((⟨x.val % 4, by omega⟩ : Fin 4) = j) := by
  unfold efx_three_pair_anchor_witness
  have hge : ¬ ((Fin.natAdd 9 x : ℕ) < 9) := by simp
  rw [dif_neg hge]
  rw [Fin.ext_iff, Fin.ext_iff]
  simp [Fin.natAdd]

lemma efx_three_pair_anchor_sanity_start_castAdd (r : ℕ) (x : Fin 9) :
    efx_three_pair_anchor_start r (Fin.castAdd (4 * r) x) = (![0, 0, 1, 1, 2, 2, 3, 3, 4] : Fin 9 → Fin 5) x := by
  unfold efx_three_pair_anchor_start
  have hlt : (Fin.castAdd (4 * r) x : ℕ) < 9 := x.is_lt
  rw [dif_pos hlt]; rfl

lemma efx_three_pair_anchor_sanity_witness_castAdd (r : ℕ) (x : Fin 9) :
    efx_three_pair_anchor_witness r (Fin.castAdd (4 * r) x) = (![0, 0, 1, 3, 2, 0, 1, 2, 3] : Fin 9 → Fin 4) x := by
  unfold efx_three_pair_anchor_witness
  have hlt : (Fin.castAdd (4 * r) x : ℕ) < 9 := x.is_lt
  rw [dif_pos hlt]; rfl

lemma efx_three_pair_anchor_sanity_values_castAdd (r : ℕ) (i : Fin 4) (x : Fin 9) :
    efx_three_pair_anchor_values r i (Fin.castAdd (4 * r) x) = efx_allsource_three_pair_values i x := by
  unfold efx_three_pair_anchor_values
  have hlt : (Fin.castAdd (4 * r) x : ℕ) < 9 := x.is_lt
  rw [dif_pos hlt]; rfl

lemma efx_three_pair_anchor_sanity_sum_base_start (i j : Fin 4) :
    (∑ g : Fin 9, if (![0, 0, 1, 1, 2, 2, 3, 3, 4] g : Fin 5) = j.castSucc then efx_allsource_three_pair_values i g else 0) =
    efx_allsource_three_pair_values i (![0, 2, 4, 6] j) + efx_allsource_three_pair_values i (![1, 3, 5, 7] j) := by
  revert i j
  decide

lemma efx_three_pair_anchor_sanity_start_bundle_sum (r : ℕ) (i j : Fin 4) :
    (∑ g : Fin (9 + 4 * r), if efx_three_pair_anchor_start r g = j.castSucc then efx_three_pair_anchor_values r i g else 0) =
    efx_allsource_three_pair_values i (![0, 2, 4, 6] j) + efx_allsource_three_pair_values i (![1, 3, 5, 7] j) + 100 * r := by
  rw [Fin.sum_univ_add]
  simp only [efx_three_pair_anchor_sanity_start_castAdd, efx_three_pair_anchor_sanity_values_castAdd,
    efx_three_pair_anchor_sanity_start_natAdd_eq, efx_three_pair_anchor_sanity_start_natAdd_val]
  rw [efx_three_pair_anchor_sanity_sum_base_start, efx_three_pair_anchor_sanity_sum_mod_four]

lemma efx_three_pair_anchor_sanity_witness_bundle_sum (r : ℕ) (i k : Fin 4) :
    (∑ h ∈ bundle_of (efx_three_pair_anchor_witness r) k, efx_three_pair_anchor_values r i h) =
    (∑ h ∈ bundle_of (![0, 0, 1, 3, 2, 0, 1, 2, 3] : Fin 9 → Fin 4) k, efx_allsource_three_pair_values i h) + 100 * r := by
  dsimp [bundle_of]
  rw [sum_filter, sum_filter, Fin.sum_univ_add]
  simp only [efx_three_pair_anchor_sanity_witness_castAdd, efx_three_pair_anchor_sanity_values_castAdd,
    efx_three_pair_anchor_sanity_witness_natAdd_eq, efx_three_pair_anchor_sanity_start_natAdd_val]
  rw [efx_three_pair_anchor_sanity_sum_mod_four]

lemma efx_three_pair_anchor_sanity_base_witness_le_plus_100 :
    ∀ i j : Fin 4,
      (∑ h ∈ bundle_of (![0, 0, 1, 3, 2, 0, 1, 2, 3] : Fin 9 → Fin 4) j, efx_allsource_three_pair_values i h) ≤
      (∑ h ∈ bundle_of (![0, 0, 1, 3, 2, 0, 1, 2, 3] : Fin 9 → Fin 4) i, efx_allsource_three_pair_values i h) + 100 := by
  decide

theorem efx_three_pair_anchor_sanity (r : ℕ) :
  (∀ i g, 0 < efx_three_pair_anchor_values r i g) ∧
  (∀ i j : Fin 4,
    (∑ g, if efx_three_pair_anchor_start r g = j.castSucc then efx_three_pair_anchor_values r i g else 0) ≤ 100*r+10) ∧
  (∀ i : Fin 4, efx_partial_nat_utility (efx_three_pair_anchor_values r) (efx_three_pair_anchor_start r) i = 100*r+10) ∧
  efx_partial_nat (efx_three_pair_anchor_values r) (efx_three_pair_anchor_start r) ∧
  is_efx_goods (fun i g => (efx_three_pair_anchor_values r i g : ℝ)) (efx_three_pair_anchor_witness r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i g
    unfold efx_three_pair_anchor_values
    split_ifs with h
    · exact efx_allsource_three_pair_sanity.1 i ⟨g.val, h⟩
    · decide
  · intro i j
    rw [efx_three_pair_anchor_sanity_start_bundle_sum]
    have hle := efx_allsource_three_pair_sanity.2.1 i j
    omega
  · intro i
    dsimp [efx_partial_nat_utility]
    rw [efx_three_pair_anchor_sanity_start_bundle_sum]
    have heq := efx_allsource_three_pair_sanity.2.2.1 i
    omega
  · intro i j hij g hg
    dsimp [efx_partial_nat_utility]
    rw [efx_three_pair_anchor_sanity_start_bundle_sum, efx_three_pair_anchor_sanity_start_bundle_sum]
    have heq := efx_allsource_three_pair_sanity.2.2.1 i
    have hle := efx_allsource_three_pair_sanity.2.1 i j
    omega
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    intro i j hij g
    refine Fin.addCases ?_ ?_ g
    · intro x hx
      rw [efx_three_pair_anchor_sanity_witness_bundle_sum, efx_three_pair_anchor_sanity_witness_bundle_sum,
        efx_three_pair_anchor_sanity_values_castAdd]
      have hx_bundle : x ∈ bundle_of (![0, 0, 1, 3, 2, 0, 1, 2, 3] : Fin 9 → Fin 4) j := by
        dsimp [bundle_of] at hx ⊢
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        rw [← efx_three_pair_anchor_sanity_witness_castAdd r x]
        exact hx
      have hbase := (is_efx_goods_nat_cast_iff _ _).mp efx_allsource_three_pair_sanity.2.2.2.2.2.1 i j hij x hx_bundle
      linarith
    · intro y hy
      rw [efx_three_pair_anchor_sanity_witness_bundle_sum, efx_three_pair_anchor_sanity_witness_bundle_sum,
        efx_three_pair_anchor_sanity_start_natAdd_val]
      have hle := efx_three_pair_anchor_sanity_base_witness_le_plus_100 i j
      linarith
