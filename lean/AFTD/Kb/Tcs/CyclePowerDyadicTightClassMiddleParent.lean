import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune

/-!
# cycle_power_dyadic_tight_class_middle_parent

Topic: combinatorics   Node: 968c48aeeae8

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

Equality in the uniform dyadic class weight bound forces each selected middle-quarter position to have its matched outer-quarter parent selected.
-/

open Finset

theorem cycle_power_dyadic_tight_class_middle_parent
    (k : ℕ) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (k + 2) b =
      (range (2 ^ (k + 2))).sum (fun i => (b i).toNat)) :
    (∀ a, 2 ^ k ≤ a → a < 2 ^ (k + 1) →
      b a = true → b (a + 2 ^ (k + 1)) = true) ∧
    (∀ a, 2 ^ (k + 1) ≤ a → a < 3 * 2 ^ k →
      b a = true → b (a - 2 ^ (k + 1)) = true) := by
  let L := 2 ^ k
  have hH : 2 ^ (k + 1) = L + L := by dsimp [L]; rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 4 * L := by dsimp [L]; rw [pow_add]; norm_num; omega
  have hlift :
      (range (2 ^ (k + 1))).sum (fun i => (cycle_power_dyadic_b_lift k b i).toNat) =
      (range L).sum (fun i => (b i).toNat) +
      (range L).sum (fun i => (b (3 * L + i)).toNat) := by
    rw [hH, sum_range_add]
    congr 1
    · apply sum_congr rfl
      intro i hi
      dsimp [cycle_power_dyadic_b_lift]
      rw [if_pos (show i < 2 ^ k from mem_range.mp hi)]
    · apply sum_congr rfl
      intro i hi
      dsimp [cycle_power_dyadic_b_lift]
      rw [if_neg (show ¬L + i < 2 ^ k by dsimp [L]; omega)]
      have he : L + i + 2 ^ (k + 1) = 3 * L + i := by omega
      rw [he]
  have hcross :
      (range (2 ^ (k + 1))).sum (fun i => (b i && b (i + 2 ^ (k + 1))).toNat) =
      (range L).sum (fun i => (b i && b (i + 2 ^ (k + 1))).toNat) +
      (range L).sum (fun i => (b (L + i) && b (3 * L + i)).toNat) := by
    rw [hH, sum_range_add]
    congr 1
    apply sum_congr rfl
    intro i hi
    have he : L + i + (L + L) = 3 * L + i := by omega
    rw [he]
  have hfull :
      (range (2 ^ (k + 2))).sum (fun i => (b i).toNat) =
      (range L).sum (fun i => (b i).toNat) +
      (range L).sum (fun i => (b (L + i)).toNat) +
      (range L).sum (fun i => (b (2 * L + i)).toNat) +
      (range L).sum (fun i => (b (3 * L + i)).toNat) := by
    rw [hD]
    exact cycle_power_dyadic_sum_range_four_blocks L (fun i => (b i).toNat)
  have hsmall := cycle_power_dyadic_tight_class_prune k b htight
  have hsplit := cycle_power_dyadic_class_weight_succ k b
  have hsum :
      (range L).sum (fun i => (b i && b (i + 2 ^ (k + 1))).toNat) +
      (range L).sum (fun i => (b (L + i) && b (3 * L + i)).toNat) =
      (range L).sum (fun i => (b (2 * L + i)).toNat) +
      (range L).sum (fun i => (b (L + i)).toNat) := by omega
  have hle0 : ∀ i ∈ range L,
      (b i && b (i + 2 ^ (k + 1))).toNat ≤ (b (2 * L + i)).toNat := by
    intro i hi
    have he : i + 2 ^ (k + 1) = 2 * L + i := by omega
    rw [he]
    exact cycle_power_dyadic_bool_and_toNat_le_right _ _
  have hle1 : ∀ i ∈ range L,
      (b (L + i) && b (3 * L + i)).toNat ≤ (b (L + i)).toNat := by
    intro i hi
    exact cycle_power_dyadic_bool_and_toNat_le_left _ _
  have hs0 := sum_le_sum hle0
  have hs1 := sum_le_sum hle1
  have he0 :
      (range L).sum (fun i => (b i && b (i + 2 ^ (k + 1))).toNat) =
      (range L).sum (fun i => (b (2 * L + i)).toNat) := by omega
  have he1 :
      (range L).sum (fun i => (b (L + i) && b (3 * L + i)).toNat) =
      (range L).sum (fun i => (b (L + i)).toNat) := by omega
  have heq0 := (sum_eq_sum_iff_of_le hle0).mp he0
  have heq1 := (sum_eq_sum_iff_of_le hle1).mp he1
  have hbool0 : ∀ a b : Bool, (a && b).toNat = b.toNat → b = true → a = true := by decide
  have hbool1 : ∀ a b : Bool, (a && b).toNat = a.toNat → a = true → b = true := by decide
  constructor
  · intro a ha0 ha1 hab
    have hi : a - L < L := by omega
    have he := heq1 (a - L) (mem_range.mpr hi)
    have hei : L + (a - L) = a := by omega
    have hep : 3 * L + (a - L) = a + 2 ^ (k + 1) := by omega
    rw [hei, hep] at he
    exact hbool1 _ _ he hab
  · intro a ha0 ha1 hab
    have hi : a - 2 ^ (k + 1) < L := by omega
    have he := heq0 (a - 2 ^ (k + 1)) (mem_range.mpr hi)
    have hei : a - 2 ^ (k + 1) + 2 ^ (k + 1) = a := by omega
    have hep : 2 * L + (a - 2 ^ (k + 1)) = a := by omega
    rw [hei, hep] at he
    exact hbool0 _ _ he hab
