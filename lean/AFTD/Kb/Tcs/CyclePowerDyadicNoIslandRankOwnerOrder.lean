import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftLow
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftHigh
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandHalfOwnerOrder
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_rank_owner_order

Topic: combinatorics   Node: b8db0ec78443

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

Under no-island class shape, tightness, exact dyadic edges and full ordinary coverage, the unique owner roots of consecutive edges are nondecreasing at every dyadic long distance.
-/

open Finset

theorem cycle_power_dyadic_no_island_rank_owner_order
    (m : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      x p a = false → x p b = true → x p c = true)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true) :
    ∀ j < m, ∀ (v : ℤ) (a b : ℕ), a < 2^j → b < 2^j →
      x (v-(a : ℤ)) a = true →
      x (v-(a : ℤ)) (a+2^m-2^j) = true →
      x (v+1-(b : ℤ)) b = true →
      x (v+1-(b : ℤ)) (b+2^m-2^j) = true → b ≤ a+1 := by
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    intro j hj v a b ha hb ha0 ha1 hb0 hb1
    by_cases hj0 : j=0
    · subst j; norm_num at ha hb; omega
    have hm : 2 ≤ m := by omega
    obtain ⟨k,hk⟩ : ∃ k, m=k+2 := ⟨m-2,by omega⟩
    subst m
    by_cases hjtop : j=k+1
    · subst j
      have hD : 2^(k+2)=2*2^(k+1) := by rw [pow_succ]; omega
      have hiA : a+2^(k+2)-2^(k+1)=a+2^(k+1) := by omega
      have hiB : b+2^(k+2)-2^(k+1)=b+2^(k+1) := by omega
      exact cycle_power_dyadic_no_island_half_owner_order k x htight hexact
        hshape hcover v a b ha hb ha0 (by simpa only [hiA] using ha1)
        hb0 (by simpa only [hiB] using hb1)
    · let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift k (x p)
      have hty : ∀ p, cycle_power_dyadic_class_weight (k+1) (y p) =
          (range (2^(k+1))).sum (fun a => (y p a).toNat) :=
        fun p => cycle_power_dyadic_tight_class_prune k (x p) (htight p)
      have hey := cycle_power_dyadic_prune_exact k x hexact
      have hsy := fun p => cycle_power_dyadic_no_island_prune k (x p) (hshape p)
      have hcy := cycle_power_dyadic_prune_cover k x htight hcover
      apply ih (k+1) (by omega) y hty hey hsy hcy j (by omega) v a b ha hb
      · simpa only [y,cycle_power_dyadic_b_lift_low k j a (by omega) ha] using ha0
      · simpa only [y,cycle_power_dyadic_b_lift_high k j a (by omega) ha] using ha1
      · simpa only [y,cycle_power_dyadic_b_lift_low k j b (by omega) hb] using hb0
      · simpa only [y,cycle_power_dyadic_b_lift_high k j b (by omega) hb] using hb1
