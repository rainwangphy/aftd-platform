import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandNoLongPrefix
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneRootSeparation
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleImpFullPrune
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneOuter
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_half_owner_order

Topic: combinatorics   Node: 07d8c29af691

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

In a tight dyadic full-coverage class model with explicit no-island shapes, the root owning the next half-radius edge is at least the root owning the preceding one. No scalar count or periodicity is assumed.
-/

open Finset

theorem cycle_power_dyadic_no_island_half_owner_order
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(k+2) →
      x p a = false → x p b = true → x p c = true)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+2) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+2)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true) :
    ∀ (v : ℤ) (a b : ℕ), a < 2^(k+1) → b < 2^(k+1) →
      x (v-(a : ℤ)) a = true →
      x (v-(a : ℤ)) (a+2^(k+1)) = true →
      x (v+1-(b : ℤ)) b = true →
      x (v+1-(b : ℤ)) (b+2^(k+1)) = true → b ≤ a+1 := by
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  have hfull (p : ℤ) (a : ℕ) (ha : a < 2^(k+1))
      (h0 : x p a = true) (h1 : x p (a+2^(k+1)) = true) :
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true := by
    by_cases hl : a < q
    · exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x p)
        (htight p) (hshape p) (a+2^(k+1)) (by omega) (by omega) h1
    · exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x p)
        (htight p) (hshape p) a (by omega) (by omega) h0
  intro v a b ha hb ha0 ha1 hb0 hb1
  by_contra hne
  have hab : a+1 < b := by omega
  let r := b-a-1
  have hr : 0 < r := by dsimp [r]; omega
  have hsum : b = a+r+1 := by dsimp [r]; omega
  have hroot : v+1-(b : ℤ)+(r : ℤ)=v-(a : ℤ) := by omega
  have hfa := hfull (v-(a : ℤ)) a ha ha0 ha1
  have hfb := hfull (v+1-(b : ℤ)) b hb hb0 hb1
  have hsep := cycle_power_dyadic_full_prune_root_separation k x
    (hexact k (by omega)) (v+1-(b : ℤ)) r hr hfb
    (by simpa only [hroot] using hfa)
  have haq : a+1 < q := by omega
  have hout := cycle_power_dyadic_full_prune_outer k (x (v-(a : ℤ))) hfa
  have hanext : x (v-(a : ℤ)) (a+1) = true := hout.1 _ haq
  have hanextH : x (v-(a : ℤ)) (a+1+2^(k+1)) = true := by
    have hh := cycle_power_dyadic_no_island_no_long_prefix k x htight hexact
      hshape hcover (v-(a : ℤ)) (a+1+2^(k+1)) (by omega) (by omega)
      (by convert ha1 using 1 <;> congr 1 <;> omega)
    exact hh
  have hroot' : v+1-((a+1 : ℕ) : ℤ)=v-(a : ℤ) := by omega
  have heA : a+1+2^(k+2)-2^(k+1)=a+1+2^(k+1) := by omega
  have heB : b+2^(k+2)-2^(k+1)=b+2^(k+1) := by omega
  have hd := cycle_power_exact_pair_unique (2^(k+2)) (2^(k+1)) x
    (hexact (k+1) (by omega)) (v+1) (a+1) b (by omega) hb
    (by simpa only [hroot'] using hanext)
    (by simpa only [hroot',heA] using hanextH) hb0
    (by simpa only [heB] using hb1)
  omega
