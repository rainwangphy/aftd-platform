import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandPowerCorner
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleCorner
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandNoLongPrefix
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandPrune
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_corner

Topic: combinatorics   Node: 0816d2240733

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Conditional uniform strong corner law for every cut of every dyadic radius in a tight two-interval full-cover model with exact dyadic edges. No scalar counts, periodicity, or aligned interval-width assumption is used.
-/

open Finset

theorem cycle_power_dyadic_no_island_corner
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
    ∀ (p : ℤ) (h : ℕ), 1 ≤ h → h < 2^m →
      x p (h-1) = true →
      x p h = true ∨ x (p+(h : ℤ)) (2^m-h-1) = true := by
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    intro p h hh0 hh1 hp
    by_cases hm2 : 2 ≤ m
    swap
    · interval_cases m
      · norm_num at hh1
        omega
      · have he : h=1 := by norm_num at hh1; omega
        subst h
        have hr := hexact 0 (by decide) (p+1)
        norm_num only [pow_zero,pow_one,sum_range_one,Nat.cast_zero,sub_zero,Nat.zero_add] at hr
        have hb : x (p+1) 0 = true := by
          cases h0 : x (p+1) 0 <;> cases h1 : x (p+1) 1 <;> simp_all
        exact Or.inr (by simpa using hb)
    obtain ⟨k,rfl⟩ : ∃ k, m=k+2 := ⟨m-2,by omega⟩
    let q := 2^k
    have hq : 0 < q := Nat.two_pow_pos _
    have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
    have hD : 2^(k+2)=4*q := by
      rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
    by_cases hsmall : h < q
    · let y : ℤ → ℕ → Bool := fun s => cycle_power_dyadic_b_lift k (x s)
      have hty := fun s => cycle_power_dyadic_tight_class_prune k (x s) (htight s)
      have hey := cycle_power_dyadic_prune_exact k x hexact
      have hsy := fun s => cycle_power_dyadic_no_island_prune k (x s) (hshape s)
      have hcy := cycle_power_dyadic_prune_cover k x htight hcover
      have hprev : y p (h-1)=true := by
        dsimp [y,cycle_power_dyadic_b_lift]
        rw [if_pos (by omega)]
        exact hp
      have hc := ih (k+1) (by omega) y hty hey hsy hcy p h hh0 (by omega) hprev
      rcases hc with hc | hc
      · left
        simpa only [y,cycle_power_dyadic_b_lift,if_pos (show h < 2^k from hsmall)] using hc
      · right
        dsimp [y,cycle_power_dyadic_b_lift] at hc
        rw [if_neg (by omega)] at hc
        have hi : 2^(k+1)-h-1+2^(k+1)=2^(k+2)-h-1 := by omega
        rwa [hi] at hc
    by_cases hlarge : 2^(k+1) < h
    · exact Or.inl (cycle_power_dyadic_no_island_no_long_prefix k x htight hexact hshape hcover
        p h hlarge hh1 hp)
    by_cases hmid : h < 2^(k+1) ∧ q < h
    · exact cycle_power_dyadic_no_island_middle_corner k x htight hexact hshape hcover
        p h hmid.2 hmid.1 hp
    have hpower : h=2^k ∨ h=2^(k+1) := by dsimp [q] at *; omega
    rcases hpower with rfl | rfl
    · apply cycle_power_dyadic_no_island_power_corner (k+2) k (by omega) x htight hexact hshape _ p hp
      intro v
      obtain ⟨a,ha,ha0,ha1⟩ := hcover (2^(k+2)-2^k-1) (by omega) (by omega) v
      refine ⟨a,by omega,ha0,?_⟩
      convert ha1 using 1 <;> congr 1 <;> omega
    · apply cycle_power_dyadic_no_island_power_corner (k+2) (k+1) (by omega) x htight hexact hshape _ p hp
      intro v
      obtain ⟨a,ha,ha0,ha1⟩ := hcover (2^(k+2)-2^(k+1)-1) (by omega) (by omega) v
      refine ⟨a,by omega,ha0,?_⟩
      convert ha1 using 1 <;> congr 1 <;> omega
