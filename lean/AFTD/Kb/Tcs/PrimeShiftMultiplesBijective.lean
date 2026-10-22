import AFTD.Prelude

/-!
# prime_shift_multiples_bijective

Topic: combinatorics   Node: 511d26aadd81

Provenance: helper lemma. arXiv:2610.24758 Lemma 1 proof

In the finite field ZMod n where n is prime, multiplication by any non-zero element s induces a bijection on ZMod n.
-/

/-- Multiplication by a non-zero element in ZMod n is bijective for prime n. -/
theorem prime_shift_multiples_bijective (n : ℕ) [Fact n.Prime] (s : ZMod n) (hs : s ≠ 0) :
    Function.Bijective (fun (k : ZMod n) => k * s) := by
  exact (Equiv.mulRight₀ s hs).bijective
