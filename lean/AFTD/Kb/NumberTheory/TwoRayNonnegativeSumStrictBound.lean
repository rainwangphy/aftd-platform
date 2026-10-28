import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# two_ray_nonnegative_sum_strict_bound

Topic: elementary_number_theory   Node: 13b04a4fbb26

Provenance: helper lemma. Helper for OP-197 / arXiv:2610.16562 Conjecture1, continuing the already verified two_ray_integer_atom_coeff_sum_le from deep session1. This closes primitive-ray denominator normalization and weighted length bookkeeping, not extraction of the two circuit rays or the box conjecture. No research advance claimed.

Under the same weighted two-ray relation, with D and a positive, a+b at most D, B nonnegative, the coordinate sum of u strictly less than B and the coordinate sum of v at most B, the coordinate sum of x is strictly less than B.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem two_ray_nonnegative_sum_strict_bound {ι : Type*} [Fintype ι]
    (u v x : ι → ℤ) (D a b : ℕ) (hD : 0 < D) (ha : 0 < a) (hcoeff : a+b ≤ D)
    (B : ℤ) (hB : 0 ≤ B) (hu : (∑ i, u i) < B) (hv : (∑ i, v i) ≤ B)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i) :
    (∑ i, x i) < B := by
  have hsum : (D : ℤ) * (∑ i, x i) =
      (a : ℤ) * (∑ i, u i) + (b : ℤ) * (∑ i, v i) := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun i _ => hrel i)
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have haz : (0 : ℤ) < a := by exact_mod_cast ha
  have hc : (a : ℤ)+(b : ℤ) ≤ D := by exact_mod_cast hcoeff
  have hu' := mul_lt_mul_of_pos_left hu haz
  have hv' := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg b : (0 : ℤ) ≤ b)
  have hm := mul_le_mul_of_nonneg_right hc hB
  nlinarith
