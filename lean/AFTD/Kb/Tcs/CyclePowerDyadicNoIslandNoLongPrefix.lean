import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneOuter
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleImpFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_no_long_prefix

Topic: combinatorics   Node: 57b51ee5afb5

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Conditional shape-model half-width theorem: a class with an initial selected interval extending strictly beyond half the radius cannot stop before the final endpoint. This uses the full covering model and does not assert the false single-class normalization.
-/

open Finset

theorem cycle_power_dyadic_no_island_no_long_prefix
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
    ∀ (p : ℤ) (h : ℕ), 2^(k+1) < h → h < 2^(k+2) →
      x p (h-1) = true → x p h = true := by
  intro p h hh0 hh1 hbefore
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  by_contra hmissing
  have hfalse : x p h = false := Bool.eq_false_iff.mpr hmissing
  have hprefix (i : ℕ) (hi : i < h) : x p i = true := by
    by_cases he : i=h-1
    · rw [he]; exact hbefore
    by_contra hne
    have hf : x p i = false := Bool.eq_false_iff.mpr hne
    have hh := hshape p i (h-1) h (by omega) (by omega) hh1 hf hbefore
    rw [hfalse] at hh
    contradiction
  have hpH : x p (2*q) = true := hprefix _ (by omega)
  have hfull := cycle_power_dyadic_no_island_middle_imp_full_prune k (x p)
    (htight p) (hshape p) (2*q) (by omega) (by omega) hpH
  have hout := cycle_power_dyadic_full_prune_outer k (x p) hfull
  have hshort : h < 3*q := by
    by_contra hne
    have hh := hout.2 h (by omega) hh1
    rw [hfalse] at hh
    contradiction
  have hp0 : x p 0 = true := hprefix _ (by omega)
  have hp3 : x p (3*q) = true := hout.2 _ (by omega) (by omega)
  obtain ⟨r, hr, hsr, hsEnd⟩ := hcover h (by omega) hh1 p
  have hrH : r < 2*q := by omega
  have hrpos : 0 < r := by
    by_contra hne
    have he : r=0 := by omega
    subst r
    simpa [hfalse] using hsEnd
  have hdup (hrq : r < q) (hs3 : x (p-(r : ℤ)) (r+3*q) = true) : False := by
    have he0 : 0+2^(k+2)-2^k=3*q := by omega
    have he1 : r+2^(k+2)-2^k=r+3*q := by omega
    have hd := cycle_power_exact_pair_unique (2^(k+2)) (2^k) x
      (hexact k (by omega)) p 0 r (by omega) (by omega)
      (by simpa using hp0) (by simpa only [Nat.cast_zero,sub_zero,he0] using hp3)
      hsr (by simpa only [he1] using hs3)
    omega
  by_cases hrq : q ≤ r
  · have hp := (cycle_power_dyadic_tight_class_middle_parent k
      (x (p-(r : ℤ))) (htight _)).1 r hrq (by omega) hsr
    have hp' : x (p-(r : ℤ)) (r+2*q) = true := by simpa only [hH] using hp
    have he0 : 0+2^(k+2)-2^(k+1)=2*q := by omega
    have he1 : r+2^(k+2)-2^(k+1)=r+2*q := by omega
    have hd := cycle_power_exact_pair_unique (2^(k+2)) (2^(k+1)) x
      (hexact (k+1) (by omega)) p 0 r (by omega) (by omega)
      (by simpa using hp0) (by simpa only [Nat.cast_zero,sub_zero,he0] using hpH)
      hsr (by simpa only [he1] using hp')
    omega
  · have hrq' : r < q := by omega
    have hnoMiddle (i : ℕ) (hi0 : q ≤ i) (hi1 : i < 3*q) :
        x (p-(r : ℤ)) i ≠ true := by
      intro hi
      have hsfull := cycle_power_dyadic_no_island_middle_imp_full_prune k
        (x (p-(r : ℤ))) (htight _) (hshape _) i hi0 hi1 hi
      have hsout := cycle_power_dyadic_full_prune_outer k (x (p-(r : ℤ))) hsfull
      exact hdup hrq' (hsout.2 (r+3*q) (by omega) (by omega))
    have hqfalse : x (p-(r : ℤ)) q = false :=
      Bool.eq_false_iff.mpr (hnoMiddle q (by omega) (by omega))
    have hrh : 3*q ≤ r+h := by
      by_contra hne
      exact hnoMiddle (r+h) (by omega) (by omega) hsEnd
    have hs3 := hshape (p-(r : ℤ)) q (r+h) (r+3*q)
      (by omega) (by omega) (by omega) hqfalse hsEnd
    exact hdup hrq' hs3
