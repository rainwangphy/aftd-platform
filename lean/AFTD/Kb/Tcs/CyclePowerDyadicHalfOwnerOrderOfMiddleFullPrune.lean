import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneRootSeparation
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicHalfOwnerFullPruneOfMiddle
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_half_owner_order_of_middle_full_prune

Topic: combinatorics   Node: ac2f850e2fa2

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

If selected middle bits force full prunes and the retained outer quarters are monotone toward the endpoints, then coverage only at the half-radius-plus-one distance forces the exact half-edge owners to be ordered by root. The structural premises remain explicit.
-/

open Finset

theorem cycle_power_dyadic_half_owner_order_of_middle_full_prune
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hleft : ∀ (p : ℤ) (a b : ℕ), a ≤ b → b < 2^k →
      x p b = true → x p a = true)
    (hright : ∀ (p : ℤ) (a b : ℕ), 3*2^k ≤ a → a ≤ b → b < 2^(k+2) →
      x p a = true → x p b = true)
    (hcover : ∀ v : ℤ, ∃ c : ℕ, c < 2^(k+2)-(2^(k+1)+1) ∧
      x (v-(c : ℤ)) c = true ∧ x (v-(c : ℤ)) (c+(2^(k+1)+1)) = true) :
    ∀ (v : ℤ) (a b : ℕ), a < 2^(k+1) → b < 2^(k+1) →
      x (v-(a : ℤ)) a = true → x (v-(a : ℤ)) (a+2^(k+1)) = true →
      x (v+1-(b : ℤ)) b = true → x (v+1-(b : ℤ)) (b+2^(k+1)) = true →
      b ≤ a+1 := by
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  have hfull := cycle_power_dyadic_half_owner_full_prune_of_middle k x hmid
  intro v a b ha hb ha0 ha1 hb0 hb1
  by_contra hne
  have hab : a+1 < b := by omega
  let r := b-a-1
  have hr : 0 < r := by dsimp [r]; omega
  have hsum : b=a+r+1 := by dsimp [r]; omega
  have hroot : v+1-(b : ℤ)+(r : ℤ)=v-(a : ℤ) := by omega
  have hfa := hfull (v-(a : ℤ)) a ha ha0 ha1
  have hfb := hfull (v+1-(b : ℤ)) b hb hb0 hb1
  have hsep := cycle_power_dyadic_full_prune_root_separation k x
    (hexact k (by omega)) (v+1-(b : ℤ)) r hr hfb
    (by simpa only [hroot] using hfa)
  have haq : a+1 < q := by omega
  have hbq : q < b := by omega
  obtain ⟨c,hc,hc0,hc1⟩ := hcover v
  have hcH : c < 2^(k+1) := by omega
  by_cases hcl : c < q-1
  · have hp := (cycle_power_dyadic_tight_class_middle_parent k
      (x (v-(c : ℤ))) (htight _)).2 (c+(2^(k+1)+1)) (by omega) (by omega) hc1
    have hi : c+(2^(k+1)+1)-2^(k+1)=c+1 := by omega
    rw [hi] at hp
    have hrt : v+1-((c+1 : ℕ) : ℤ)=v-(c : ℤ) := by omega
    have hiC : c+1+2^(k+2)-2^(k+1)=c+(2^(k+1)+1) := by omega
    have hiB : b+2^(k+2)-2^(k+1)=b+2^(k+1) := by omega
    have hu := cycle_power_exact_pair_unique (2^(k+2)) (2^(k+1)) x
      (hexact (k+1) (by omega)) (v+1) (c+1) b (by omega) hb
      (by simpa only [hrt] using hp) (by simpa only [hrt,hiC] using hc1)
      hb0 (by simpa only [hiB] using hb1)
    omega
  · by_cases hch : q ≤ c
    · have hp := (cycle_power_dyadic_tight_class_middle_parent k
        (x (v-(c : ℤ))) (htight _)).1 c (by omega) (by omega) hc0
      have hiC : c+2^(k+2)-2^(k+1)=c+2^(k+1) := by omega
      have hiA : a+2^(k+2)-2^(k+1)=a+2^(k+1) := by omega
      have hu := cycle_power_exact_pair_unique (2^(k+2)) (2^(k+1)) x
        (hexact (k+1) (by omega)) v c a hcH ha hc0
        (by simpa only [hiC] using hp) ha0 (by simpa only [hiA] using ha1)
      omega
    · have hcq : c=q-1 := by omega
      have hcf : ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x (v-(c : ℤ))) i = true := by
        intro i hi
        dsimp [cycle_power_dyadic_b_lift]
        split_ifs with hil
        · exact hleft (v-(c : ℤ)) i c (by omega) (by omega) hc0
        · have he : c+(2^(k+1)+1)=3*2^k := by omega
          apply hright (v-(c : ℤ)) (3*2^k) (i+2^(k+1)) (by omega) (by omega) (by omega)
          simpa only [he] using hc1
      let s := c-a
      have hs : 0 < s := by dsimp [s]; omega
      have hrt : v-(c : ℤ)+(s : ℤ)=v-(a : ℤ) := by dsimp [s]; omega
      have hssep := cycle_power_dyadic_full_prune_root_separation k x
        (hexact k (by omega)) (v-(c : ℤ)) s hs hcf
        (by simpa only [hrt] using hfa)
      dsimp [s] at hssep
      omega
