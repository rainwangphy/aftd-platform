import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints

/-!
# cycle_power_dyadic_boundary_pair_of_alternating

Topic: combinatorics   Node: 7a3515b31a0d

Provenance: helper lemma. Helper for RT-1 (OP-205, arXiv:2610.15635): rungs of cycle_power_dyadic_alternating_half_model (the even and odd halves of the bit-1 classes of an alternating endpoint-only dyadic model form a model one exponent lower)

In an exactly dyadically covered model at exponent M >= 2 whose bit 1 alternates along the roots, every class has boundary pairing: offset 2^M - 2 is selected iff offset 1 is (exactness at distance 2^M - 2 at vertex p counts the pair (p, p + 2^M - 2) of the class at p and the pair (p, p + 2^M - 2) of the class at p - 1, whose bit 1 is the negation of bit 1 at p).
-/

theorem cycle_power_dyadic_boundary_pair_of_alternating (M : ℕ) (hM : 2 ≤ M) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < M, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^M-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1) :
    ∀ p : ℤ, x p (2^M - 2) = x p 1 := by
  intro p
  have hend := cycle_power_dyadic_exact_endpoints M (by omega) x hexact
  have h := hexact 1 (by omega) p
  have hM4 : 4 ≤ 2 ^ M := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hM
  have e1 : 1 + 2 ^ M - 2 = 2 ^ M - 1 := by omega
  have e0 : 0 + 2 ^ M - 2 = 2 ^ M - 2 := by omega
  rw [pow_one, Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [Nat.cast_zero, sub_zero, Nat.cast_one] at h
  rw [e0, e1] at h
  have ha := halt (p - 1)
  rw [sub_add_cancel] at ha
  have hp0 := (hend p).1
  have hq1 := (hend (p - 1)).2
  rw [hp0, hq1] at h
  rw [ha]
  cases h2 : x p (2 ^ M - 2) <;> cases h3 : x (p - 1) 1 <;> simp_all
