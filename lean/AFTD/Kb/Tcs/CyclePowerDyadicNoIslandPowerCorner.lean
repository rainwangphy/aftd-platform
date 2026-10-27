import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_no_island_power_corner

Topic: combinatorics   Node: 5a566083c3c7

Provenance: helper lemma. Conditional structural helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The no-island hypothesis remains explicit and unproved for the general periodic model. These helpers do not settle the covering-number conjecture, and no research advance is claimed.

Conditional uniform dyadic corner law: in tight two-interval class profiles with exact dyadic edges and one ordinary-neighbour family, a selected prefix endpoint at 2^j-1 forces either the next prefix bit or the corresponding endpoint in the class rooted 2^j later. No periodicity, scalar count, or half-width normalization is assumed.
-/

open Finset

theorem cycle_power_dyadic_no_island_power_corner
    (m j : ℕ) (hjm : j < m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < m, ∀ v : ℤ, (range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^i)).toNat) = 1)
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      x p a = false → x p b = true → x p c = true)
    (hcover : ∀ v : ℤ, ∃ a : ℕ, a < 2^j+1 ∧
      x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+2^m-2^j-1) = true) :
    ∀ p : ℤ, x p (2^j-1) = true →
      x p (2^j) = true ∨ x (p+((2^j : ℕ) : ℤ)) (2^m-2^j-1) = true := by
  intro p hp
  let D := 2^m
  let h := 2^j
  have hhpos : 0 < h := Nat.two_pow_pos j
  have hDh : 2*h ≤ D := by
    have he : 2^(j+1) ≤ 2^m :=
      Nat.pow_le_pow_right (by decide) (show j+1 ≤ m by omega)
    rw [pow_succ] at he
    dsimp [D,h]
    omega
  have hhD : h < D := by omega
  by_cases hnext : x p h = true
  · exact Or.inl hnext
  right
  have hfalse : x p h = false := Bool.eq_false_iff.mpr hnext
  have hroot (s : ℤ) : x s 0 = true ∧ x s (D-1) = true := by
    have hh := hexact 0 (by omega) s
    norm_num only [pow_zero, sum_range_one, Nat.cast_zero, sub_zero, Nat.zero_add] at hh
    change (x s 0 && x s (D-1)).toNat = 1 at hh
    cases h0 : x s 0 <;> cases h1 : x s (D-1) <;> simp [h0,h1] at hh ⊢
  have hprefix (a : ℕ) (ha : a < h) : x p a = true := by
    by_cases he : a=h-1
    · rw [he]; exact hp
    by_contra hne
    have hx : x p a = false := Bool.eq_false_iff.mpr hne
    have hh := hshape p a (h-1) h (by omega) (by omega) hhD hx hp
    rw [hfalse] at hh
    contradiction
  obtain ⟨a, ha, hxa, hxb⟩ := hcover (p+(h : ℤ))
  change a < h+1 at ha
  let r := h-a
  have har : a+r=h := by dsimp [r]; omega
  have hrle : r ≤ h := by omega
  have harg : p+(h : ℤ)-(a : ℤ)=p+(r : ℤ) := by dsimp [r]; omega
  have hidx : a+D-h-1=D-1-r := by dsimp [r]; omega
  change x (p+(h : ℤ)-(a : ℤ)) a = true at hxa
  change x (p+(h : ℤ)-(a : ℤ)) (a+D-h-1) = true at hxb
  rw [harg] at hxa hxb
  rw [hidx] at hxb
  by_cases hr0 : r=0
  · have haeq : a=h := by dsimp [r] at hr0; omega
    rw [hr0, Nat.cast_zero, add_zero, haeq, hfalse] at hxa
    contradiction
  by_cases hrh : r=h
  · have he : D-1-h=D-h-1 := by omega
    rw [hrh, he] at hxb
    exact hxb
  have hrpos : 0 < r := by omega
  have hrlt : r < h := by omega
  let b := h-1-r
  have hb : b < h := by dsimp [b]; omega
  have hvold : p+((h-1 : ℕ) : ℤ)-((h-1 : ℕ) : ℤ)=p := by omega
  have hvnew : p+((h-1 : ℕ) : ℤ)-(b : ℤ)=p+(r : ℤ) := by dsimp [b]; omega
  have holdidx : (h-1)+D-h=D-1 := by omega
  have hnewidx : b+D-h=D-1-r := by dsimp [b]; omega
  by_cases hbtrue : x (p+(r : ℤ)) b = true
  · have he := cycle_power_exact_pair_unique D h x (hexact j hjm)
      (p+((h-1 : ℕ) : ℤ)) (h-1) b (by omega) hb
      (by rw [hvold]; exact hp)
      (by rw [hvold, holdidx]; exact (hroot p).2)
      (by rw [hvnew]; exact hbtrue)
      (by rw [hvnew, hnewidx]; exact hxb)
    dsimp [b] at he
    omega
  have hbfalse : x (p+(r : ℤ)) b = false := Bool.eq_false_iff.mpr hbtrue
  have hasuffix (c : ℕ) (hc0 : a ≤ c) (hc1 : c < D) :
      x (p+(r : ℤ)) c = true := by
    by_cases he : c=a
    · rw [he]; exact hxa
    exact hshape (p+(r : ℤ)) b a c (by dsimp [b,r]; omega) (by omega) hc1 hbfalse hxa
  by_cases hj0 : j=0
  · have hh : h=1 := by simp [h,hj0]
    omega
  have hjpos : 1 ≤ j := by omega
  let q := 2^(j-1)
  have hqpos : 0 < q := Nat.two_pow_pos _
  have hhq : h=2*q := by
    dsimp [h,q]
    conv_lhs => rw [show j=(j-1)+1 by omega]
    rw [pow_succ]; omega
  by_cases hrq : q ≤ r
  · have hbq : b < q := by dsimp [b]; omega
    have hh := (cycle_power_dyadic_tight_class_parent m j hjpos hjm
      (x (p+(r : ℤ))) (htight (p+(r : ℤ)))) b hb
    have hc := hh.1 hbq
    change x (p+(r : ℤ)) (b+D-h) = true →
      x (p+(r : ℤ)) b = true at hc
    rw [hnewidx] at hc
    have hf := hc hxb
    rw [hbfalse] at hf
    contradiction
  have hrq' : r < q := by omega
  have hqpre : x p q = true := hprefix q (by omega)
  have hparent := (cycle_power_dyadic_tight_class_parent m j hjpos hjm
    (x p) (htight p)) q (by omega)
  have htail0 := hparent.2 (by dsimp [q]; omega) hqpre
  change x p (q+D-h) = true at htail0
  have htailidx : q+D-h=D-q := by omega
  rw [htailidx] at htail0
  have htail (c : ℕ) (hc0 : D-q ≤ c) (hc1 : c < D) : x p c = true := by
    by_cases he : c=D-q
    · rw [he]; exact htail0
    exact hshape p h (D-q) c (by omega) (by omega) hc1 hfalse htail0
  have hB : x p (r+D-q) = true := htail _ (by omega) (by omega)
  have hC : x (p+(r : ℤ)) (D-q) = true := hasuffix _ (by omega) (by omega)
  have hv0 : p+(r : ℤ)-(r : ℤ)=p := by omega
  have he := cycle_power_exact_pair_unique D q x (hexact (j-1) (by omega))
    (p+(r : ℤ)) r 0 hrq' hqpos
    (by rw [hv0]; exact hprefix r hrlt)
    (by rw [hv0]; exact hB)
    (by simpa only [Nat.cast_zero, sub_zero] using (hroot (p+(r : ℤ))).1)
    (by simpa only [Nat.cast_zero, sub_zero, Nat.zero_add] using hC)
  omega
