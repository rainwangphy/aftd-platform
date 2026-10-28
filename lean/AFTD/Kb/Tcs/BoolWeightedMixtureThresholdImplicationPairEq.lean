import AFTD.Prelude
import AFTD.Kb.Tcs.BoolThresholdPairSum

/-!
# bool_weighted_mixture_threshold_implication_pair_eq

Topic: combinatorics   Node: 5c11b19bc510

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

The common-threshold coupling preserves a pair mass exactly whenever selection of the first coordinate implies selection of the second in every original profile.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem bool_weighted_mixture_threshold_implication_pair_eq
    {ι κ : Type*} (S : Finset ι) (w : ι → ℕ) (B : ι → κ → Bool)
    (a b : κ) (hab : ∀ i ∈ S, B i a = true → B i b = true) :
    let N := S.sum w
    let c := fun j => S.sum (fun i => w i * (B i j).toNat)
    (range N).sum (fun r => (decide (r < c a) && decide (r < c b)).toNat) =
      S.sum (fun i => w i * (B i a && B i b).toNat) := by
  dsimp only
  let c := fun j => S.sum (fun i => w i * (B i j).toNat)
  have hle : c a ≤ c b := by
    apply sum_le_sum
    intro i hi
    cases ha : B i a
    · simp [ha]
    · simp [ha, hab i hi ha]
  have hbound : c a ≤ S.sum w := by
    apply sum_le_sum
    intro i hi
    cases B i a <;> simp
  rw [bool_threshold_pair_sum]
  rw [min_eq_left hle, min_eq_right hbound]
  apply sum_congr rfl
  intro i hi
  cases ha : B i a
  · simp [ha]
  · simp [ha, hab i hi ha]
