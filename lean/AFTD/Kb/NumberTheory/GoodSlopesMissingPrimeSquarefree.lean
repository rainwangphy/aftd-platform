import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMemIff
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G

/-!
# good_slopes_missing_prime_squarefree

Topic: elementary_number_theory   Node: 3d239ca5fc84

Provenance: helper lemma. Squarefree case of the prime-residue assertion in arXiv:2611.01465, Theorem 3.1, generalizing good_slopes_missing_prime105.

Let n be squarefree and nonzero, let the prime p divide n, and let f be a permutation modulo n. Then some residue modulo p is missed by every good slope of f.
-/

open Finset

private lemma good_slopes_missing_prime_squarefree_div_ne_zero (n p : ℕ) (hn : Squarefree n) (hp : Nat.Prime p) (hd : p ∣ n) :
    ((n / p : ℕ) : ZMod p) ≠ 0 := by
  intro h0
  have h_dvd : p ∣ (n / p) := (ZMod.natCast_eq_zero_iff (n / p) p).mp h0
  have hp2 : p * p ∣ n := by
    rcases hd with ⟨k, rfl⟩
    rcases h_dvd with ⟨m, hm⟩
    have : (p * k) / p = k := Nat.mul_div_cancel_left k (Nat.Prime.pos hp)
    rw [this] at hm
    subst hm
    exact ⟨m, by ring⟩
  exact hp.not_isUnit (hn p hp2)

private lemma good_slopes_missing_prime_squarefree_zmod_prime_sum_pow_pred (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (∑ x : ZMod p, x ^ (p - 1)) = -1 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hp_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.1.two_le
  have h0 : (0 : ZMod p) ^ (p - 1) = 0 := zero_pow (ne_of_gt hp_pos)
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff, mem_singleton, φ]
    constructor
    · rintro ⟨u, rfl⟩; exact Units.ne_zero u
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  calc
    ∑ x : ZMod p, x ^ (p - 1) = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ (p - 1) := by
      rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, h0, add_zero]
    _ = ∑ x : (ZMod p)ˣ, (x ^ (p - 1) : ZMod p) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = if Fintype.card (ZMod p) - 1 ∣ p - 1 then -1 else 0 := FiniteField.sum_pow_units (ZMod p) (p - 1)
    _ = -1 := by
      rw [hcard]
      simp

private lemma good_slopes_missing_prime_squarefree_zmod_prime_sum_affine_pow (p : ℕ) [hp : Fact (Nat.Prime p)] (x y : ZMod p) :
    (∑ a : ZMod p, (y + a * x) ^ (p - 1)) = if x = 0 then 0 else -1 := by
  split_ifs with hx
  · subst hx
    simp
  · have hbij : Function.Bijective (fun a : ZMod p => y + a * x) := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have : a * x = b * x := add_left_cancel hab
        exact mul_right_cancel₀ hx this
      · intro z
        refine ⟨(z - y) / x, ?_⟩
        dsimp
        rw [div_mul_cancel₀ (z - y) hx, add_sub_cancel]
    rw [hbij.sum_comp (fun u => u ^ (p - 1))]
    exact good_slopes_missing_prime_squarefree_zmod_prime_sum_pow_pred p

private lemma good_slopes_missing_prime_squarefree_sum_indicator_lift (n p : ℕ) [NeZero n] [NeZero p] (hd : p ∣ n) (hp : Fact (Nat.Prime p)) :
    (∑ x : ZMod n, if ZMod.castHom hd (ZMod p) x = 0 then (0 : ZMod p) else (-1 : ZMod p)) = ((n / p : ℕ) : ZMod p) := by
  let c := ZMod.castHom hd (ZMod p)
  let F : ZMod p → ZMod p := fun y => if y = 0 then 0 else -1
  have hfib := (sum_fiberwise_of_maps_to (g := c) (s := univ) (t := univ) (fun _ _ => mem_univ _) (fun x => F (c x))).symm
  change (∑ x : ZMod n, F (c x)) = ((n / p : ℕ) : ZMod p)
  rw [hfib]
  have hsurj := ZMod.castHom_surjective hd
  have hfiber_eq : ∀ y : ZMod p, #{x : ZMod n | c x = y} = #{x : ZMod n | c x = 0} := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range c.toAddMonoidHom (hsurj y) (hsurj 0)
  have hstep1 : (∑ j : ZMod p, ∑ i ∈ univ with c i = j, F (c i)) =
      ∑ j : ZMod p, (#{i : ZMod n | c i = j} : ZMod p) * F j := by
    apply sum_congr rfl
    intro y _
    have : (∑ x ∈ univ.filter (fun x => c x = y), F (c x)) = ∑ x ∈ univ.filter (fun x => c x = y), F y := by
      apply sum_congr rfl
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [hx]
    rw [this, sum_const, nsmul_eq_mul]
  rw [hstep1]
  simp_rw [hfiber_eq]
  have hsum_card : ∑ y : ZMod p, #{x : ZMod n | c x = y} = n := by
    have h := (card_eq_sum_card_fiberwise (f := c) (s := (univ : Finset (ZMod n))) (t := (univ : Finset (ZMod p))) (fun _ _ => mem_univ _)).symm
    rw [card_univ, ZMod.card] at h
    exact h
  simp_rw [hfiber_eq] at hsum_card
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hsum_card
  have hcard_val : #{x : ZMod n | c x = 0} = n / p :=
    Nat.eq_div_of_mul_eq_right (Nat.Prime.ne_zero hp.1) hsum_card
  rw [← mul_sum]
  have hs : ({0} : Finset (ZMod p)) ⊆ univ := subset_univ _
  have hsplit : (∑ y : ZMod p, F y) = (∑ y ∈ ({0} : Finset (ZMod p)), F y) + (∑ y ∈ univ \ ({0} : Finset (ZMod p)), F y) := by
    rw [← sum_sdiff hs, add_comm]
  have hzero : (∑ y ∈ ({0} : Finset (ZMod p)), F y) = 0 := by simp [F]
  have hrest : (∑ y ∈ univ \ ({0} : Finset (ZMod p)), F y) = ∑ y ∈ univ \ ({0} : Finset (ZMod p)), (-1 : ZMod p) := by
    apply sum_congr rfl
    intro y hy
    simp only [mem_sdiff, mem_singleton] at hy
    simp [F, hy.2]
  have hsumF : (∑ y : ZMod p, F y) = 1 := by
    rw [hsplit, hzero, zero_add, hrest, sum_const, card_sdiff_of_subset hs, card_singleton, card_univ, ZMod.card, nsmul_eq_mul]
    have hsub : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have h1 : (1 : ℕ) ≤ p := hp.1.pos
      have h2 := Nat.cast_sub (R := ZMod p) h1
      rw [h2]
      simp
    rw [hsub]
    ring
  rw [hsumF, mul_one, hcard_val]

theorem good_slopes_missing_prime_squarefree (n p : ℕ) [NeZero n] [NeZero p] (hn : Squarefree n) (hp : Nat.Prime p) (hd : p ∣ n) (f : Equiv.Perm (ZMod n)) : ∃ a : ZMod p, ∀ m ∈ good_slopes n f, ZMod.castHom hd (ZMod p) m ≠ a := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod n →+* ZMod p := ZMod.castHom hd (ZMod p)
  by_contra h_all
  push Not at h_all
  choose m hm hma using h_all
  let total : ZMod p := ∑ x : ZMod n, (c x) ^ (p - 1)
  have hsum (a : ZMod p) : (∑ x : ZMod n, (c (f x) + a * c x) ^ (p - 1)) = total := by
    have hbij : Function.Bijective (fun x : ZMod n => f x + m a * x) :=
      (good_slopes_mem_iff n f (m a)).mp (hm a)
    calc
      _ = ∑ x : ZMod n, (c (f x + m a * x)) ^ (p - 1) := by
        apply sum_congr rfl
        intro x _
        rw [map_add, map_mul, hma a]
      _ = total := hbij.sum_comp (fun x => (c x) ^ (p - 1))
  have houter : (∑ a : ZMod p, ∑ x : ZMod n, (c (f x) + a * c x) ^ (p - 1)) = 0 := by
    simp_rw [hsum]
    simp [total]
  have hinner : (∑ a : ZMod p, ∑ x : ZMod n, (c (f x) + a * c x) ^ (p - 1)) =
      ∑ x : ZMod n, if c x = 0 then 0 else (-1 : ZMod p) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    exact good_slopes_missing_prime_squarefree_zmod_prime_sum_affine_pow p (c x) (c (f x))
  have heq : (∑ x : ZMod n, if c x = 0 then 0 else (-1 : ZMod p)) = 0 := hinner.symm.trans houter
  rw [good_slopes_missing_prime_squarefree_sum_indicator_lift n p hd ‹_›] at heq
  exact good_slopes_missing_prime_squarefree_div_ne_zero n p hn hp hd heq
