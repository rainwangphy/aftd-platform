import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntegerPrimitiveRayCoeffCoprime
import AFTD.Kb.NumberTheory.TwoRayIntegerAtomCoeffSumLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# two_ray_integer_atom_coeff_sum_le_primitive

Topic: elementary_number_theory   Node: 3508eece54f1

Provenance: helper lemma. Helper for OP-197 / arXiv:2610.16562 Conjecture1, continuing the already verified two_ray_integer_atom_coeff_sum_le from deep session1. This closes primitive-ray denominator normalization and weighted length bookkeeping, not extraction of the two circuit rays or the box conjecture. No research advance claimed.

For an additive subgroup of integer-valued functions, let x have no proper nonzero nonnegative subgroup subvector. Given nonnegative primitive u,v in the subgroup, u nonzero, D positive, a,b smaller than D, and D*x=a*u+b*v, one has a+b at most D. Individual coefficient coprimality is not assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem two_ray_integer_atom_coeff_sum_le_primitive {ι : Type*}
    (M : AddSubgroup (ι → ℤ)) (u v x : ι → ℤ)
    (huM : u ∈ M) (hvM : v ∈ M) (hxM : x ∈ M)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hu : u ≠ 0)
    (hmin : ∀ y ∈ M, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y = 0 ∨ y = x)
    (hprimu : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ u i) → d ∣ 1)
    (hprimv : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ v i) → d ∣ 1)
    (D a b : ℕ) (hD : 0 < D) (ha : a < D) (hb : b < D)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i) :
    a + b ≤ D := by
  let d := Nat.gcd (Nat.gcd a b) D
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ hD
  have hdD : d ∣ D := Nat.gcd_dvd_right _ _
  have hda : d ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)
  have hdb : d ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)
  have hDD : d * (D/d) = D := Nat.mul_div_cancel' hdD
  have haa : d * (a/d) = a := Nat.mul_div_cancel' hda
  have hbb : d * (b/d) = b := Nat.mul_div_cancel' hdb
  have hD' : 0 < D/d := by nlinarith
  have ha' : a/d < D/d := by nlinarith
  have hb' : b/d < D/d := by nlinarith
  have hg : Nat.gcd a b = d * Nat.gcd (a/d) (b/d) := by
    conv_lhs => rw [← haa, ← hbb]
    rw [Nat.gcd_mul_left]
  have hgdiv : Nat.gcd (a/d) (b/d) = (Nat.gcd a b)/d := by
    have hh := Nat.mul_div_cancel' (Nat.gcd_dvd_left (Nat.gcd a b) D)
    exact Nat.eq_of_mul_eq_mul_left hd (hg.symm.trans hh.symm)
  have htr' : Nat.Coprime (Nat.gcd (a/d) (b/d)) (D/d) := by
    rw [hgdiv]
    exact Nat.coprime_div_gcd_div_gcd hd
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hDz : (d : ℤ) * ((D/d : ℕ) : ℤ) = D := by exact_mod_cast hDD
  have haz : (d : ℤ) * ((a/d : ℕ) : ℤ) = a := by exact_mod_cast haa
  have hbz : (d : ℤ) * ((b/d : ℕ) : ℤ) = b := by exact_mod_cast hbb
  have hrel' (i : ι) :
      ((D/d : ℕ) : ℤ) * x i = ((a/d : ℕ) : ℤ) * u i + ((b/d : ℕ) : ℤ) * v i := by
    have he : (d : ℤ) * (((D/d : ℕ) : ℤ) * x i -
        ((a/d : ℕ) : ℤ) * u i - ((b/d : ℕ) : ℤ) * v i) = 0 := by
      calc
        _ = ((d : ℤ) * ((D/d : ℕ) : ℤ)) * x i -
            ((d : ℤ) * ((a/d : ℕ) : ℤ)) * u i -
            ((d : ℤ) * ((b/d : ℕ) : ℤ)) * v i := by ring
        _ = 0 := by rw [hDz, haz, hbz, hrel]; ring
    have hh := (mul_eq_zero.mp he).resolve_left hdne
    linarith
  have hca := integer_primitive_ray_coeff_coprime u v x hprimv (D/d) (a/d) (b/d) htr' hrel'
  have hcb : Nat.Coprime (b/d) (D/d) := by
    apply integer_primitive_ray_coeff_coprime v u x hprimu (D/d) (b/d) (a/d)
    · rw [Nat.gcd_comm (b/d) (a/d)]
      exact htr'
    · intro i
      simpa only [add_comm] using hrel' i
  have hh := two_ray_integer_atom_coeff_sum_le M u v x huM hvM hxM hu0 hv0 hu hmin
    (D/d) (a/d) (b/d) hD' ha' hb' hca hcb hrel'
  nlinarith
