import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandRankOwnerOrder

/-!
# cycle_power_dyadic_outer_eighth_owner_order

Topic: combinatorics   Node: 50d59c08617e

Provenance: helper lemma. Uniform structural helpers for OP-205 / RT-1, following arXiv:2610.15635. The new eight-block local extension remains unproved. These lemmas retain explicit shape/selected-missing hypotheses and do not settle any graph covering value; no research advance is claimed.

In a tight exact fully ordinarily covered dyadic model of radius2^(k+3), monotone outer eighths imply that roots owning consecutive edges of distance7*2^k are nondecreasing. Counts and periodicity are not assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_outer_eighth_owner_order
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+3) (x p) =
      (range (2^(k+3))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+3, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+3)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+3) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+3)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (houter : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^k → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 7*2^k ≤ a → a ≤ b → b < 2^(k+3) →
        x p a = true → x p b = true)) :
    ∀ (v : ℤ) (a b : ℕ), a < 2^k → b < 2^k →
      x (v-(a : ℤ)) a = true →
      x (v-(a : ℤ)) (a+7*2^k) = true →
      x (v+1-(b : ℤ)) b = true →
      x (v+1-(b : ℤ)) (b+7*2^k) = true → b ≤ a+1 := by
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hP₁ : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hP₂ : 2^(k+2)=4*q := by rw [show k+2=(k+1)+1 by omega,pow_succ,hP₁]; omega
  have hP₃ : 2^(k+3)=8*q := by rw [show k+3=(k+2)+1 by omega,pow_succ,hP₂]; omega
  let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift (k+1) (x p)
  let z : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift k (y p)
  have hyT := fun p => cycle_power_dyadic_tight_class_prune (k+1) (x p) (htight p)
  have hyE := cycle_power_dyadic_prune_exact (k+1) x hexact
  have hyC := cycle_power_dyadic_prune_cover (k+1) x htight hcover
  have hzT := fun p => cycle_power_dyadic_tight_class_prune k (y p) (hyT p)
  have hzE := cycle_power_dyadic_prune_exact k y hyE
  have hzC := cycle_power_dyadic_prune_cover k y hyT hyC
  have hzLow (p : ℤ) (i : ℕ) (hi : i < q) : z p i = x p i := by
    dsimp [z,y,cycle_power_dyadic_b_lift]
    rw [if_pos hi,if_pos (by omega)]
  have hzHigh (p : ℤ) (i : ℕ) (hi₀ : q ≤ i) (hi₁ : i < 2*q) :
      z p i = x p (i+6*q) := by
    dsimp [z,y,cycle_power_dyadic_b_lift]
    rw [if_neg (by omega),if_neg (by omega)]
    congr 1
    omega
  have hzShape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(k+1) →
      z p a = false → z p b = true → z p c = true := by
    intro p a b c hab hbc hc ha hb
    by_cases hbq : b < q
    · have haq : a < q := by omega
      rw [hzLow p a haq] at ha
      rw [hzLow p b hbq] at hb
      have hh := (houter p).1 a b (by omega) hbq hb
      rw [ha] at hh
      contradiction
    · have hcb : q ≤ c := by omega
      rw [hzHigh p b (by omega) (by omega)] at hb
      rw [hzHigh p c hcb (by omega)]
      exact (houter p).2 (b+6*q) (c+6*q) (by dsimp [q] at *; omega)
        (by omega) (by omega) hb
  have hzPair (p : ℤ) (a : ℕ) (ha : a < q) :
      z p (a+2^(k+1)-2^k) = x p (a+7*q) := by
    have hi : a+2^(k+1)-2^k=a+q := by dsimp [q]; omega
    rw [hi,hzHigh p (a+q) (by omega) (by omega)]
    congr 1
    omega
  intro v a b ha hb ha₀ ha₁ hb₀ hb₁
  apply cycle_power_dyadic_no_island_rank_owner_order (k+1) z hzT hzE hzShape hzC
    k (by omega) v a b ha hb
  · simpa only [hzLow _ a ha] using ha₀
  · simpa only [hzPair _ a ha] using ha₁
  · simpa only [hzLow _ b hb] using hb₀
  · simpa only [hzPair _ b hb] using hb₁
