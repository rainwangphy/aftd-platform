import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes

/-!
# good_slopes_missing_prime105

Topic: elementary_number_theory   Node: 441aea291f90

Provenance: helper lemma. The modulus 105 case of the prime-residue part of Theorem 2.5 in arXiv:2611.04551, which cites arXiv:2611.01465 Theorem 3.1.

For a permutation modulo 105 and each prime divisor p, some residue modulo p is not attained by any good slope.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
private theorem aftd_missing_prime_power (p : ℕ) [NeZero p] (hd : p ∣ 105)
    (e : ℕ) (f : Equiv.Perm (ZMod 105))
    (hlocal : ∀ x y : ZMod p, (∑ a : ZMod p, (y+a*x)^e) = if x=0 then 0 else -1)
    (hnonzero : (∑ x : ZMod 105, if ZMod.castHom hd (ZMod p) x = 0 then 0 else (-1 : ZMod p)) ≠ 0) :
    ∃ a : ZMod p, ∀ m ∈ good_slopes 105 f, ZMod.castHom hd (ZMod p) m ≠ a := by
  classical
  let c : ZMod 105 →+* ZMod p := ZMod.castHom hd (ZMod p)
  by_contra hn
  push_neg at hn
  choose m hm hma using hn
  let total : ZMod p := ∑ x : ZMod 105, (c x)^e
  have hsum (a : ZMod p) : (∑ x : ZMod 105, (c (f x)+a*c x)^e) = total := by
    have hbij : Function.Bijective (fun x : ZMod 105 => f x + m a*x) := (Finset.mem_filter.mp (hm a)).2
    calc
      _ = ∑ x : ZMod 105, (c (f x + m a*x))^e := by
        apply Finset.sum_congr rfl
        intro x _
        rw [map_add,map_mul,hma a]
      _ = total := hbij.sum_comp (fun x => (c x)^e)
  have houter : (∑ a : ZMod p, ∑ x : ZMod 105, (c (f x)+a*c x)^e) = 0 := by
    simp_rw [hsum]
    simp [total]
  have hinner : (∑ a : ZMod p, ∑ x : ZMod 105, (c (f x)+a*c x)^e) =
      ∑ x : ZMod 105, if c x = 0 then 0 else -1 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact hlocal (c x) (c (f x))
  exact hnonzero (hinner.symm.trans houter)

theorem good_slopes_missing_prime105 (p : ℕ) [NeZero p] (hp : p = 3 ∨ p = 5 ∨ p = 7) (hd : p ∣ 105) (f : Equiv.Perm (ZMod 105)) : ∃ a : ZMod p, ∀ m ∈ good_slopes 105 f, ZMod.castHom hd (ZMod p) m ≠ a := by
  rcases hp with rfl | rfl | rfl
  · letI : NeZero 3 := ⟨by decide⟩
    apply aftd_missing_prime_power 3 hd 2 f
    · decide +revert
    · decide +revert
  · letI : NeZero 5 := ⟨by decide⟩
    apply aftd_missing_prime_power 5 hd 4 f
    · decide +revert
    · decide +revert
  · letI : NeZero 7 := ⟨by decide⟩
    apply aftd_missing_prime_power 7 hd 6 f
    · decide +revert
    · decide +revert
