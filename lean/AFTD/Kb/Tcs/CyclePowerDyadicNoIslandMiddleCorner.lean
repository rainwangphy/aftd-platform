import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneRootSeparation
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneOuter
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleImpFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_middle_corner

Topic: combinatorics   Node: 4039d0501622

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Conditional uniform corner law for every cut strictly between one quarter and one half of the dyadic radius, under tight two-interval profiles, exact dyadic ownership, and full ordinary coverage.
-/

open Finset

theorem cycle_power_dyadic_no_island_middle_corner
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
    ∀ (p : ℤ) (h : ℕ), 2^k < h → h < 2^(k+1) →
      x p (h-1) = true →
      x p h = true ∨ x (p+(h : ℤ)) (2^(k+2)-h-1) = true := by
  intro p h hh0 hh1 hbefore
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  by_cases hnext : x p h = true
  · exact Or.inl hnext
  right
  by_contra htarget
  have hfalse : x p h = false := Bool.eq_false_iff.mpr hnext
  have hprefix (i : ℕ) (hi : i < h) : x p i = true := by
    by_cases he : i=h-1
    · rw [he]; exact hbefore
    by_contra hne
    have hf : x p i = false := Bool.eq_false_iff.mpr hne
    have hh := hshape p i (h-1) h (by omega) (by omega) (by omega) hf hbefore
    rw [hfalse] at hh
    contradiction
  let Full (s : ℤ) := ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x s) i = true
  have hfullp : Full p := cycle_power_dyadic_no_island_middle_imp_full_prune k (x p)
    (htight p) (hshape p) q (by omega) (by omega) (hprefix q (by omega))
  have hout := cycle_power_dyadic_full_prune_outer k (x p) hfullp
  have hsep (s : ℤ) (r : ℕ) (hr : 0 < r)
      (hf : Full s) (hg : Full (s+(r : ℤ))) : q ≤ r :=
    cycle_power_dyadic_full_prune_root_separation k x (hexact k (by omega)) s r hr hf hg
  have hfullh : Full (p+(h : ℤ)) := by
    obtain ⟨a, ha, hxa, hxb⟩ := hcover (2*q-1) (by omega) (by omega) (p+(h : ℤ))
    have haH : a ≤ 2*q := by omega
    let s := p+(h : ℤ)-(a : ℤ)
    change x s a = true at hxa
    change x s (a+(2*q-1)) = true at hxb
    by_cases ha0 : a=0
    · have he : s=p+(h : ℤ) := by dsimp [s]; omega
      rw [ha0] at hxb
      have hbit : x (p+(h : ℤ)) (2*q-1) = true := by simpa only [he,Nat.zero_add] using hxb
      exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x (p+(h : ℤ)))
        (htight _) (hshape _) (2*q-1) (by omega) (by omega) hbit
    have hapos : 0 < a := by omega
    have hprev : x s (a-1) = false := by
      by_contra hne
      have hprevT : x s (a-1) = true := by
        cases hb : x s (a-1) <;> simp_all
      have hv0 : p+(h : ℤ)-1-((h-1 : ℕ) : ℤ)=p := by omega
      have hv1 : p+(h : ℤ)-1-((a-1 : ℕ) : ℤ)=s := by dsimp [s]; omega
      have hi0 : h-1+2^(k+2)-2^(k+1)=h+2*q-1 := by omega
      have hi1 : a-1+2^(k+2)-2^(k+1)=a+(2*q-1) := by omega
      have holdEnd : x p (h+2*q-1) = true := hout.2 _ (by omega) (by omega)
      have he := cycle_power_exact_pair_unique (2^(k+2)) (2^(k+1)) x
        (hexact (k+1) (by omega)) (p+(h : ℤ)-1) (h-1) (a-1)
        (by omega) (by omega) (by simpa only [hv0] using hbefore)
        (by simpa only [hv0,hi0] using holdEnd) (by simpa only [hv1] using hprevT)
        (by simpa only [hv1,hi1] using hxb)
      have heah : a=h := by omega
      have hes : s=p := by dsimp [s]; omega
      rw [hes,heah,hfalse] at hxa
      contradiction
    have hfw : Full s := by
      by_cases haq : q ≤ a
      · exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x s)
          (htight _) (hshape _) a haq (by omega) hxa
      · have hbit := hshape s (a-1) a q (by omega) (by omega) (by omega) hprev hxa
        exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x s)
          (htight _) (hshape _) q (by omega) (by omega) hbit
    by_cases hal : a < h
    · have he : p+((h-a : ℕ) : ℤ)=s := by dsimp [s]; omega
      have hf : Full (p+((h-a : ℕ) : ℤ)) := by rw [he]; exact hfw
      have hd := hsep p (h-a) (by omega) hfullp hf
      have ho := cycle_power_dyadic_full_prune_outer k (x s) hfw
      have hh := ho.1 (a-1) (by omega)
      rw [hprev] at hh
      contradiction
    · by_cases hae : a=h
      · have hes : s=p := by dsimp [s]; omega
        rw [hes,hae,hfalse] at hxa
        contradiction
      · have he : s+((a-h : ℕ) : ℤ)=p := by dsimp [s]; omega
        have hf : Full (s+((a-h : ℕ) : ℤ)) := by rw [he]; exact hfullp
        have hd := hsep s (a-h) (by omega) hfw hf
        omega
  obtain ⟨b, hb, hxb, hxe⟩ := hcover (2^(k+2)-h-1) (by omega) (by omega) (p+(h : ℤ))
  have hble : b ≤ h := by omega
  let r := h-b
  let s := p+(r : ℤ)
  have hroot : p+(h : ℤ)-(b : ℤ)=s := by dsimp [s,r]; omega
  have hidx : b+(2^(k+2)-h-1)=2^(k+2)-1-r := by dsimp [r]; omega
  rw [hroot] at hxb hxe
  rw [hidx] at hxe
  have hrpos : 0 < r := by
    by_contra hne
    have he : r=0 := by omega
    have hb' : b=h := by dsimp [r] at he; omega
    have hs : s=p := by dsimp [s]; omega
    rw [hs,hb',hfalse] at hxb
    contradiction
  have hrl : r < h := by
    by_contra hne
    have hb' : b=0 := by dsimp [r] at *; omega
    have hs : s=p+(h : ℤ) := by dsimp [s,r]; omega
    have hi : 2^(k+2)-1-r=2^(k+2)-h-1 := by dsimp [r]; omega
    rw [hs,hi] at hxe
    exact htarget hxe
  by_cases hrq : q ≤ r
  · have hfw : Full s := cycle_power_dyadic_no_island_middle_imp_full_prune k (x s)
      (htight _) (hshape _) (2^(k+2)-1-r) (by omega) (by omega) hxe
    have he : s+((h-r : ℕ) : ℤ)=p+(h : ℤ) := by dsimp [s]; omega
    have hf : Full (s+((h-r : ℕ) : ℤ)) := by rw [he]; exact hfullh
    have hd := hsep s (h-r) (by omega) hfw hf
    omega
  · have hrq' : r < q := by omega
    have hnoMiddle (i : ℕ) (hi0 : q ≤ i) (hi1 : i < 3*q) : x s i ≠ true := by
      intro hi
      have hfw : Full s := cycle_power_dyadic_no_island_middle_imp_full_prune k (x s)
        (htight _) (hshape _) i hi0 hi1 hi
      have hd := hsep p r hrpos hfullp hfw
      omega
    have hbq : b < q := by
      by_contra hne
      exact hnoMiddle b (by omega) (by dsimp [r] at *; omega) hxb
    have hqf : x s q = false := Bool.eq_false_iff.mpr (hnoMiddle q (by omega) (by omega))
    have ht : x s (q-1-r) = true := by
      by_contra hne
      have hf : x s (q-1-r) = false := Bool.eq_false_iff.mpr hne
      have hh := hshape s (q-1-r) b q (by dsimp [r] at *; omega)
        (by omega) (by omega) hf hxb
      rw [hqf] at hh
      contradiction
    have hv0 : p+(q : ℤ)-1-((q-1 : ℕ) : ℤ)=p := by omega
    have hv1 : p+(q : ℤ)-1-((q-1-r : ℕ) : ℤ)=s := by dsimp [s]; omega
    have hi0 : q-1+2^(k+2)-2^k=2^(k+2)-1 := by omega
    have hi1 : q-1-r+2^(k+2)-2^k=2^(k+2)-1-r := by omega
    have he := cycle_power_exact_pair_unique (2^(k+2)) (2^k) x
      (hexact k (by omega)) (p+(q : ℤ)-1) (q-1) (q-1-r) (by omega) (by omega)
      (by simpa only [hv0] using hprefix (q-1) (by omega))
      (by simpa only [hv0,hi0] using hout.2 (2^(k+2)-1) (by omega) (by omega))
      (by simpa only [hv1] using ht) (by simpa only [hv1,hi1] using hxe)
    omega
