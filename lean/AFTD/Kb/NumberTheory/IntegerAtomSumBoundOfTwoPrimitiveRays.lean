import AFTD.Prelude
import AFTD.Kb.NumberTheory.TwoRayIntegerAtomCoeffSumLePrimitive
import AFTD.Kb.NumberTheory.TwoRayNonnegativeSumBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# integer_atom_sum_bound_of_two_primitive_rays

Topic: elementary_number_theory   Node: a7f1044019ad

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

In an additive subgroup of finite integer vectors, an element with no proper nonzero nonnegative subgroup subvector has coordinate sum at most B if it is a nonnegative rational combination of two nonzero nonnegative primitive subgroup vectors, each of sum at most the nonnegative integer B. The common denominator and coefficients are arbitrary positive/nonnegative integers; coefficients smaller than the denominator are not assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem integer_atom_sum_bound_of_two_primitive_rays {ι : Type*} [Fintype ι]
    (M : AddSubgroup (ι → ℤ)) (u v x : ι → ℤ)
    (huM : u ∈ M) (hvM : v ∈ M) (hxM : x ∈ M)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hu : u ≠ 0) (hv : v ≠ 0)
    (hmin : ∀ y ∈ M, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y = 0 ∨ y = x)
    (hprimu : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ u i) → d ∣ 1)
    (hprimv : ∀ d : ℕ, (∀ i, (d : ℤ) ∣ v i) → d ∣ 1)
    (D a b : ℕ) (hD : 0 < D)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i)
    (B : ℤ) (hB : 0 ≤ B) (hub : (∑ i, u i) ≤ B) (hvb : (∑ i, v i) ≤ B) :
    (∑ i, x i) ≤ B := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  by_cases ha : D ≤ a
  · have hau : ∀ i, u i ≤ x i := by
      intro i
      have hai : (D : ℤ) ≤ a := by exact_mod_cast ha
      have hh := mul_le_mul_of_nonneg_right hai (hu0 i)
      have hbv : 0 ≤ (b : ℤ) * v i := mul_nonneg (Nat.cast_nonneg _) (hv0 i)
      have hr := hrel i
      nlinarith
    have hx := (hmin u huM hu0 hau).resolve_left hu
    simpa only [← hx] using hub
  by_cases hb : D ≤ b
  · have hav : ∀ i, v i ≤ x i := by
      intro i
      have hbi : (D : ℤ) ≤ b := by exact_mod_cast hb
      have hh := mul_le_mul_of_nonneg_right hbi (hv0 i)
      have hau : 0 ≤ (a : ℤ) * u i := mul_nonneg (Nat.cast_nonneg _) (hu0 i)
      have hr := hrel i
      nlinarith
    have hx := (hmin v hvM hv0 hav).resolve_left hv
    simpa only [← hx] using hvb
  have hc := two_ray_integer_atom_coeff_sum_le_primitive M u v x huM hvM hxM hu0 hv0 hu
    hmin hprimu hprimv D a b hD (by omega) (by omega) hrel
  exact two_ray_nonnegative_sum_bound u v x D a b hD hc B hB hub hvb hrel
