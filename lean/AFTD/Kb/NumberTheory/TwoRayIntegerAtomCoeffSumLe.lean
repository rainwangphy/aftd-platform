import AFTD.Prelude
import AFTD.Kb.NumberTheory.CoprimeResidueSmallRectangle
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# two_ray_integer_atom_coeff_sum_le

Topic: elementary_number_theory   Node: 88cd33cc9e54

Provenance: helper lemma. Supporting modular proof for the two-dimensional cone atom bound, a standard fact described in Combinatorial Commutative Algebra, Example 7.19 (https://pages.uoregon.edu/njp/MS.pdf). Used toward the four-support reduction for OP-197, arXiv:2610.16562 Conjecture 1; no new research-level result is claimed.

Let x be an atom in the nonnegative part of an additive subgroup of integer-valued functions. If D*x=a*u+b*v for nonnegative subgroup elements u,v, u is nonzero, a,b<D, and a,b are each coprime to D, then a+b<=D. This is the coefficient triangle inequality for the two-ray reduction.
-/

open Finset
set_option maxHeartbeats 2000000

theorem two_ray_integer_atom_coeff_sum_le {ι : Type*}
    (M : AddSubgroup (ι → ℤ)) (u v x : ι → ℤ)
    (huM : u ∈ M) (hvM : v ∈ M) (hxM : x ∈ M)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hu : u ≠ 0)
    (hmin : ∀ y ∈ M, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y = 0 ∨ y = x)
    (D a b : ℕ) (hD : 0 < D) (ha : a < D) (hb : b < D)
    (hca : Nat.Coprime a D) (hcb : Nat.Coprime b D)
    (hrel : ∀ i, (D : ℤ) * x i = (a : ℤ) * u i + (b : ℤ) * v i) :
    a + b ≤ D := by
  classical
  by_contra hbad
  obtain ⟨k, hkD, hk0, hka, hkb⟩ := coprime_residue_small_rectangle
    D a b hD ha hb hca hcb (by omega)
  let r := (k * a) % D
  let s := (k * b) % D
  let qa := (k * a) / D
  let qb := (k * b) / D
  let y := (k : ℤ) • x - (qa : ℤ) • u - (qb : ℤ) • v
  have hyM : y ∈ M := M.sub_mem (M.sub_mem (M.zsmul_mem hxM (k : ℤ))
    (M.zsmul_mem huM (qa : ℤ))) (M.zsmul_mem hvM (qb : ℤ))
  have hqa : (r : ℤ) + (D : ℤ) * (qa : ℤ) = (k : ℤ) * (a : ℤ) := by
    dsimp [r, qa]
    exact_mod_cast Nat.mod_add_div (k * a) D
  have hqb : (s : ℤ) + (D : ℤ) * (qb : ℤ) = (k : ℤ) * (b : ℤ) := by
    dsimp [s, qb]
    exact_mod_cast Nat.mod_add_div (k * b) D
  have hyr : ∀ i, (D : ℤ) * y i = (r : ℤ) * u i + (s : ℤ) * v i := by
    intro i
    dsimp [y]
    calc
      (D : ℤ) * ((k : ℤ) * x i - (qa : ℤ) * u i - (qb : ℤ) * v i) =
          (k : ℤ) * ((D : ℤ) * x i) -
            ((D : ℤ) * (qa : ℤ)) * u i - ((D : ℤ) * (qb : ℤ)) * v i := by ring
      _ = (r : ℤ) * u i + (s : ℤ) * v i := by
        rw [hrel]
        linear_combination -(u i) * hqa - (v i) * hqb
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    apply (mul_nonneg_iff_of_pos_left hDz).mp
    rw [hyr]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hu0 i))
      (mul_nonneg (Nat.cast_nonneg _) (hv0 i))
  have hyle : ∀ i, y i ≤ x i := by
    intro i
    apply (mul_le_mul_iff_right₀ hDz).mp
    rw [hyr, hrel]
    have hrle : (r : ℤ) ≤ a := by exact_mod_cast Nat.le_of_lt hka
    have hsle : (s : ℤ) ≤ b := by exact_mod_cast hkb
    exact add_le_add (mul_le_mul_of_nonneg_right hrle (hu0 i))
      (mul_le_mul_of_nonneg_right hsle (hv0 i))
  obtain ⟨i, hi⟩ : ∃ i, 0 < u i := by
    by_contra hnone
    push Not at hnone
    apply hu
    funext i
    exact le_antisymm (hnone i) (hu0 i)
  have hr0 : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh : Nat.ModEq D (k * a) (0 * a) := by
      change (k * a) % D = (0 * a) % D
      simpa [r] using hz
    have hc := Nat.ModEq.cancel_right_of_coprime hca.symm hh
    have hk : k = 0 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hkD, Nat.zero_mod] using hc
    omega
  have hyne : y ≠ 0 := by
    intro hz
    have he := hyr i
    rw [hz] at he
    simp only [Pi.zero_apply, mul_zero] at he
    have hp : (0 : ℤ) < (r : ℤ) * u i := mul_pos (by exact_mod_cast hr0) hi
    have hn := mul_nonneg (Nat.cast_nonneg s) (hv0 i)
    linarith
  have hyx : y ≠ x := by
    intro heq
    have he := hyr i
    rw [heq, hrel] at he
    have hrlt : (r : ℤ) < a := by exact_mod_cast hka
    have hsle : (s : ℤ) ≤ b := by exact_mod_cast hkb
    have hp := mul_pos (sub_pos.mpr hrlt) hi
    have hn := mul_nonneg (sub_nonneg.mpr hsle) (hv0 i)
    nlinarith
  exact (hmin y hyM hy0 hyle).elim hyne hyx
