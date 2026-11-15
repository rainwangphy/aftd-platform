import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMissingPrimeSquarefree
import AFTD.Kb.NumberTheory.ZeroMemGoodSlopes

/-!
# good_slopes_unit_cover_squarefree

Topic: elementary_number_theory   Node: 3121d1b93743

Provenance: helper lemma. Squarefree specialization of the unit-cover part of arXiv:2611.01465 Theorem 3.1, using good_slopes_missing_prime_squarefree.

For every nonzero squarefree modulus and permutation, some unit can be added to all its good slopes to make them units.
-/

open scoped Function

theorem good_slopes_unit_cover_squarefree (n : ℕ) [NeZero n] (hn : Squarefree n) (f : Equiv.Perm (ZMod n)) : ∃ c : ZMod n, IsUnit c ∧ ∀ m ∈ good_slopes n f, IsUnit (m+c) := by
  have isUnit_iff_forall_prime (x : ZMod n) :
      IsUnit x ↔ ∀ (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ n), ZMod.castHom hd (ZMod p) x ≠ 0 := by
    have hunit : IsUnit x ↔ Nat.Coprime x.val n := by
      simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime x.val n)
    rw [hunit]
    constructor
    · intro hcop p hp hd hz
      have hcast : ZMod.castHom hd (ZMod p) x = (x.val : ZMod p) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val x]
        exact map_natCast _ _
      rw [hcast] at hz
      have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).mp hz
      have : ∃ q, Nat.Prime q ∧ q ∣ x.val ∧ q ∣ n := ⟨p, hp, hdvd, hd⟩
      exact Nat.Prime.not_coprime_iff_dvd.mpr this hcop
    · intro h
      by_contra hnc
      obtain ⟨p, hp, hpx, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have hz : (x.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x.val p).mpr hpx
      have hcast : ZMod.castHom hpn (ZMod p) x = (x.val : ZMod p) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val x]
        exact map_natCast _ _
      exact (h p hp hpn) (hcast.trans hz)
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      ∃ a : ZMod p, ∀ m ∈ good_slopes n f, ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) m ≠ a := by
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have : NeZero p := ⟨hp_prime.ne_zero⟩
    exact good_slopes_missing_prime_squarefree n p hn hp_prime (Nat.dvd_of_mem_primeFactors hp) f
  choose a ha using h
  let rem : ℕ → ℕ := fun p => if hp : p ∈ n.primeFactors then (- a p hp).val else 0
  have hrem (p : ℕ) (hp : p ∈ n.primeFactors) : (rem p : ZMod p) = - a p hp := by
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have : NeZero p := ⟨hp_prime.ne_zero⟩
    dsimp [rem]
    rw [dif_pos hp]
    exact ZMod.natCast_zmod_val (- a p hp)
  have hs : ∀ p ∈ n.primeFactors, p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpp : (↑n.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset rem id n.primeFactors hs hpp
  let c : ZMod n := (k : ZMod n)
  have hc_cast (p : ℕ) (hp : p ∈ n.primeFactors) (hd : p ∣ n) :
      ZMod.castHom hd (ZMod p) c = - a p hp := by
    have hk_mod : (k : ZMod p) = (rem p : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' k (rem p) p).mpr (hk p hp)
    calc
      ZMod.castHom hd (ZMod p) c = (k : ZMod p) := map_natCast (ZMod.castHom hd (ZMod p)) k
      _ = (rem p : ZMod p) := hk_mod
      _ = - a p hp := hrem p hp
  have hshift (m : ZMod n) (hm : m ∈ good_slopes n f) : IsUnit (m + c) := by
    rw [isUnit_iff_forall_prime]
    intro p hp hd
    have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne n⟩
    rw [map_add, hc_cast p hp_mem hd]
    intro hzero
    apply ha p hp_mem m hm
    have : ZMod.castHom hd (ZMod p) m - a p hp_mem = 0 := by
      simpa only [sub_eq_add_neg] using hzero
    exact sub_eq_zero.mp this
  refine ⟨c, ?_, hshift⟩
  have hz := zero_mem_good_slopes n f
  simpa using hshift 0 hz
