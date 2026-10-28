import AFTD.Prelude

/-!
# integer_primitive_ray_coeff_coprime

Topic: elementary_number_theory   Node: 8d3cefe6af8f

Provenance: helper lemma. Helper for OP-197 / arXiv:2610.16562 Conjecture1, continuing the already verified two_ray_integer_atom_coeff_sum_le from deep session1. This closes primitive-ray denominator normalization and weighted length bookkeeping, not extraction of the two circuit rays or the box conjecture. No research advance claimed.

Let u,v,x be integer-valued functions, with v primitive in the sense that every common natural divisor of its coordinates divides one. If gcd(a,b) is coprime to D and D*x=a*u+b*v coordinatewise, then a is coprime to D.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem integer_primitive_ray_coeff_coprime {ι : Type*}
    (u v x : ι → ℤ)
    (hprimv : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ v i) → d ∣ 1)
    (D a b : ℕ) (htr : Nat.Coprime (Nat.gcd a b) D)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i) :
    Nat.Coprime a D := by
  let g := Nat.gcd a D
  have hbg : Nat.Coprime b g := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    dsimp [g]
    rw [← Nat.gcd_assoc, Nat.gcd_comm b a]
    exact htr.gcd_eq_one
  have hgD : (g : ℤ) ∣ (D : ℤ) := by exact_mod_cast Nat.gcd_dvd_right a D
  have hga : (g : ℤ) ∣ (a : ℤ) := by exact_mod_cast Nat.gcd_dvd_left a D
  have hvdiv (i : ι) : (g : ℤ) ∣ v i := by
    have hp : (g : ℤ) ∣ (b : ℤ) * v i := by
      have hh := dvd_sub (dvd_mul_of_dvd_left hgD (x i)) (dvd_mul_of_dvd_left hga (u i))
      rw [hrel] at hh
      simpa only [add_sub_cancel_left] using hh
    apply Int.dvd_of_dvd_mul_right_of_gcd_one hp
    simpa [Int.gcd, Nat.gcd_comm] using hbg.gcd_eq_one
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp (hprimv g hvdiv))
