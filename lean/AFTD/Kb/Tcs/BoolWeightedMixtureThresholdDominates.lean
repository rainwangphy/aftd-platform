import AFTD.Prelude
import AFTD.Kb.Tcs.BoolThresholdMarginalSum
import AFTD.Kb.Tcs.BoolThresholdPairSum

/-!
# bool_weighted_mixture_threshold_dominates

Topic: combinatorics   Node: f47fb4c28be9

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

Every finite natural-weighted mixture of Boolean profiles admits a common-threshold coupling with the same coordinate masses, at least the old mass on every selected pair, and every original pointwise Boolean implication preserved.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem bool_weighted_mixture_threshold_dominates
    {ι κ : Type*} (S : Finset ι) (w : ι → ℕ) (B : ι → κ → Bool) :
    let N := S.sum w
    let c := fun j => S.sum (fun i => w i * (B i j).toNat)
    let T := fun r j => decide (r < c j)
    (∀ j, (range N).sum (fun r => (T r j).toNat) = c j) ∧
    (∀ a b, S.sum (fun i => w i * (B i a && B i b).toNat) ≤
      (range N).sum (fun r => (T r a && T r b).toNat)) ∧
    (∀ a b, (∀ i ∈ S, B i a = true → B i b = true) →
      ∀ r, T r a = true → T r b = true) := by
  dsimp only
  let N := S.sum w
  let c := fun j => S.sum (fun i => w i * (B i j).toNat)
  have hbound (j : κ) : c j ≤ N := by
    apply sum_le_sum
    intro i hi
    cases B i j <;> simp
  have hpairL (a b : κ) : S.sum (fun i => w i * (B i a && B i b).toNat) ≤ c a := by
    apply sum_le_sum
    intro i hi
    cases B i a <;> cases B i b <;> simp
  have hpairR (a b : κ) : S.sum (fun i => w i * (B i a && B i b).toNat) ≤ c b := by
    apply sum_le_sum
    intro i hi
    cases B i a <;> cases B i b <;> simp
  constructor
  · intro j
    rw [bool_threshold_marginal_sum]
    exact min_eq_right (hbound j)
  constructor
  · intro a b
    rw [bool_threshold_pair_sum]
    apply le_min
    · exact (hpairL a b).trans (hbound a)
    · exact le_min (hpairL a b) (hpairR a b)
  · intro a b hab r hr
    have hle : c a ≤ c b := by
      apply sum_le_sum
      intro i hi
      cases ha : B i a
      · simp [ha]
      · simp [ha, hab i hi ha]
    simp only [decide_eq_true_eq] at hr ⊢
    exact lt_of_lt_of_le hr hle
