import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodicOfPrime
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BrgcInverseConcat

/-!
# bitword_rotate_iterate_cut

Topic: combinatorics   Node: 0faeb44353e8

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Cyclically rotating an n-bit nonconstant word left by a positions exchanges its prefix of length a and its suffix of length b, where a+b=n.
-/

theorem bitword_rotate_iterate_cut {n a b u v : ℕ} (hn : 2 ≤ n) (hab : a + b = n)
    (hu : u < 2 ^ a) (hv : v < 2 ^ b)
    (h0 : 0 < 2 ^ b * u + v) (h1 : 2 ^ b * u + v < 2 ^ n - 1) :
    (bitword_rotate n)^[a] (2 ^ b * u + v) = 2 ^ a * v + u := by
  obtain ⟨heq, hpos, _⟩ :=
    bitword_is_aperiodic_of_prime_iterate_eq_mod n hn (2 ^ b * u + v) h0 h1 a
  have hpow : 2 ^ a * 2 ^ b = 2 ^ n := by rw [← pow_add, hab]
  have hpred : 2 ^ n - 1 + 1 = 2 ^ n := by
    have := Nat.two_pow_pos n
    omega
  have he : 2 ^ a * (2 ^ b * u + v) =
      (2 ^ n - 1) * u + (2 ^ a * v + u) := by
    calc
      _ = (2 ^ a * 2 ^ b) * u + 2 ^ a * v := by ring
      _ = 2 ^ n * u + 2 ^ a * v := by rw [hpow]
      _ = (2 ^ n - 1 + 1) * u + 2 ^ a * v := by rw [hpred]
      _ = _ := by ring
  have hmod : (2 ^ a * (2 ^ b * u + v)) % (2 ^ n - 1) =
      (2 ^ a * v + u) % (2 ^ n - 1) := by rw [he]; simp
  rw [hmod] at heq
  have hbound : 2 ^ a * v + u < 2 ^ n := by
    have hh := brgc_aux_concat_bound hv hu
    simpa only [show b + a = n by omega] using hh
  have hlt : 2 ^ a * v + u < 2 ^ n - 1 := by
    by_contra hnot
    have hh : 2 ^ a * v + u = 2 ^ n - 1 := by omega
    rw [hh, Nat.mod_self] at heq
    omega
  rwa [Nat.mod_eq_of_lt hlt] at heq
