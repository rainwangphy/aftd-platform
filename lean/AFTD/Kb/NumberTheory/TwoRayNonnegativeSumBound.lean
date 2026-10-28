import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# two_ray_nonnegative_sum_bound

Topic: elementary_number_theory   Node: cb836b97c3da

Provenance: helper lemma. Helper for OP-197 / arXiv:2610.16562 Conjecture1, continuing the already verified two_ray_integer_atom_coeff_sum_le from deep session1. This closes primitive-ray denominator normalization and weighted length bookkeeping, not extraction of the two circuit rays or the box conjecture. No research advance claimed.

For finite integer-valued functions u,v,x and natural D,a,b with D positive and a+b at most D, if D*x=a*u+b*v coordinatewise and both u and v have coordinate sum at most B, where B is a nonnegative integer, then x has coordinate sum at most B.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem two_ray_nonnegative_sum_bound {ι : Type*} [Fintype ι]
    (u v x : ι → ℤ) (D a b : ℕ) (hD : 0 < D) (hcoeff : a+b ≤ D)
    (B : ℤ) (hB : 0 ≤ B) (hu : (∑ i, u i) ≤ B) (hv : (∑ i, v i) ≤ B)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i) :
    (∑ i, x i) ≤ B := by
  have hsum : (D : ℤ) * (∑ i, x i) =
      (a : ℤ) * (∑ i, u i) + (b : ℤ) * (∑ i, v i) := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun i _ => hrel i)
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hc : (a : ℤ)+(b : ℤ) ≤ D := by exact_mod_cast hcoeff
  have hu' := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg a : (0 : ℤ) ≤ a)
  have hv' := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg b : (0 : ℤ) ≤ b)
  have hm := mul_le_mul_of_nonneg_right hc hB
  nlinarith
