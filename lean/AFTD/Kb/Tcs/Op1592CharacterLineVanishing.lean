import AFTD.Prelude

/-!
# op_1592_character_line_vanishing

Topic: combinatorics   Node: 11a8c837e0da

Provenance: helper lemma. The necessity argument, arXiv:2611.14754, Section 3.

For finite additive commutative groups, a function whose sums over translates of a homomorphic image are constant has zero Fourier coefficient at any nontrivial character that is trivial on that image.
-/

open Finset
set_option maxHeartbeats 4000000

theorem op_1592_character_line_vanishing
    {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (phi : H →+ G) (chi : AddChar G ℂ) (hchi : chi ≠ 0)
    (hphi : ∀ t : H, chi (phi t) = 1) (f : G → ℂ) (C : ℂ)
    (hline : ∀ x : G, (∑ t : H, f (x + phi t)) = C) :
    ∑ x : G, f x * chi x = 0 := by
  classical
  have hchar : (∑ x : G, chi x) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hchi
  have hshift (t : H) : (∑ x : G, f (x + phi t) * chi (x + phi t)) =
      ∑ x : G, f x * chi x := by
    exact (Equiv.addRight (phi t)).bijective.sum_comp (fun x => f x * chi x)
  have hsum1 : (∑ x : G, ∑ t : H, f (x + phi t) * chi (x + phi t)) =
      (Fintype.card H : ℂ) * (∑ x : G, f x * chi x) := by
    rw [Finset.sum_comm]
    simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum2 : (∑ x : G, ∑ t : H, f (x + phi t) * chi (x + phi t)) = 0 := by
    calc
      _ = ∑ x : G, (∑ t : H, f (x + phi t)) * chi x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        rw [chi.map_add_eq_mul, hphi, mul_one]
      _ = C * (∑ x : G, chi x) := by simp_rw [hline]; rw [Finset.mul_sum]
      _ = 0 := by rw [hchar, mul_zero]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp (hsum1.symm.trans hsum2)).resolve_left hcard
