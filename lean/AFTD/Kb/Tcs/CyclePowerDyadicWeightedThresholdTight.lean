import AFTD.Prelude
import AFTD.Kb.Tcs.BoolWeightedMixtureThresholdDominates
import AFTD.Kb.Tcs.CyclePowerDyadicWeightedThresholdWeightGe
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_weighted_threshold_tight

Topic: combinatorics   Node: 3132b3da0714

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

For positive dyadic exponent, every common-threshold profile below total mixture mass is tight when all original profiles of the natural-weighted finite mixture are tight.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_weighted_threshold_tight
    {ι : Type*} (m : ℕ) (hm : 1 ≤ m) (S : Finset ι) (w : ι → ℕ)
    (B : ι → ℕ → Bool)
    (htight : ∀ i ∈ S, cycle_power_dyadic_class_weight m (B i) =
      (range (2^m)).sum (fun a => (B i a).toNat)) :
    let N := S.sum w
    let c := fun j => S.sum (fun i => w i * (B i j).toNat)
    ∀ r < N, cycle_power_dyadic_class_weight m (fun j => decide (r < c j)) =
      (range (2^m)).sum (fun a => (decide (r < c a)).toNat) := by
  dsimp only
  let N := S.sum w
  let c := fun j => S.sum (fun i => w i * (B i j).toNat)
  let T := fun r j => decide (r < c j)
  change ∀ r < N, cycle_power_dyadic_class_weight m (T r) =
    (range (2^m)).sum (fun a => (T r a).toNat)
  have hmargin := (bool_weighted_mixture_threshold_dominates S w B).1
  have hcard : (range N).sum (fun r => (range (2^m)).sum (fun a => (T r a).toNat)) =
      S.sum (fun i => w i * (range (2^m)).sum (fun a => (B i a).toNat)) := by
    rw [sum_comm]
    simp_rw [show ∀ a, (range N).sum (fun r => (T r a).toNat) = c a from hmargin]
    dsimp only [c]
    rw [sum_comm]
    simp only [mul_sum]
  have hW := cycle_power_dyadic_weighted_threshold_weight_ge m S w B
  have hOld : S.sum (fun i => w i * cycle_power_dyadic_class_weight m (B i)) =
      S.sum (fun i => w i * (range (2^m)).sum (fun a => (B i a).toNat)) := by
    exact sum_congr rfl (fun i hi => congrArg (fun z => w i * z) (htight i hi))
  have hTotal : (range N).sum (fun r => (range (2^m)).sum (fun a => (T r a).toNat)) ≤
      (range N).sum (fun r => cycle_power_dyadic_class_weight m (T r)) := by
    calc
      _ = S.sum (fun i => w i * (range (2^m)).sum (fun a => (B i a).toNat)) := hcard
      _ = S.sum (fun i => w i * cycle_power_dyadic_class_weight m (B i)) := hOld.symm
      _ ≤ _ := hW
  intro r hr
  have hle := cycle_power_dyadic_class_weight_le m hm (T r)
  by_contra hne
  have hlt : cycle_power_dyadic_class_weight m (T r) <
      (range (2^m)).sum (fun a => (T r a).toNat) := by omega
  have hs := sum_lt_sum
    (fun q (_ : q ∈ range N) => cycle_power_dyadic_class_weight_le m hm (T q))
    ⟨r, mem_range.mpr hr, hlt⟩
  omega
