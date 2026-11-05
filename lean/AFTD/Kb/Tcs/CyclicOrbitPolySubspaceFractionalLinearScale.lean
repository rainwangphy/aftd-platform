import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicOrbitPolySubspace
import AFTD.Kb.Tcs.CyclicOrbitDenomNeZero
import AFTD.Kb.Tcs.CyclicOrbitPolySubspacePowMem

/-!
# cyclic_orbit_poly_subspace_fractional_linear_scale

Topic: information   Node: e38e207c0e39

Provenance: helper lemma. arXiv:2611.04947 Lemma 3.2, eq (5)

Given fields B and M with an algebra structure of M over B, a natural number r with 2 ≤ r, elements x, y ∈ M such that (minpoly B x).natDegree ≥ 2 * r - 1, elements a, b, c, d ∈ B with a * d - b * c ≠ 0, and y = (algebraMap B M a * x + algebraMap B M b) / (algebraMap B M c * x + algebraMap B M d), the pointwise scalar multiple (algebraMap B M c * x + algebraMap B M d) ^ (r - 1) • cyclic_orbit_poly_subspace B r y equals cyclic_orbit_poly_subspace B r x.
-/

open Pointwise Polynomial

lemma cyclic_orbit_poly_subspace_fractional_linear_scale_poly_deg
    {B : Type*} [Field B] (a b c d : B) (i : ℕ) (r : ℕ) (hi : i < r) :
    natDegree ((C a * X + C b) ^ i * (C c * X + C d) ^ (r - 1 - i) : B[X]) < r := by
  have h1 : natDegree (C a * X + C b : B[X]) ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (natDegree_mul_le) ?_
      simp [natDegree_C, natDegree_X]
    · omega
  have h2 : natDegree (C c * X + C d : B[X]) ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (natDegree_mul_le) ?_
      simp [natDegree_C, natDegree_X]
    · omega
  refine lt_of_le_of_lt (natDegree_mul_le) ?_
  refine lt_of_le_of_lt (add_le_add (natDegree_pow_le.trans (Nat.mul_le_mul_left i h1))
    (natDegree_pow_le.trans (Nat.mul_le_mul_left (r - 1 - i) h2))) ?_
  simp only [mul_one]
  omega

lemma cyclic_orbit_poly_subspace_fractional_linear_scale_aeval_mem
    {B M : Type*} [Field B] [Field M] [Algebra B M]
    (r : ℕ) (x : M) (p : B[X]) (hp : p.natDegree < r) :
    aeval x p ∈ cyclic_orbit_poly_subspace B r x := by
  rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [map_sum]
  refine Submodule.sum_mem _ ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rw [map_mul, aeval_C, aeval_X_pow]
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (cyclic_orbit_poly_subspace_pow_mem r x ⟨i, hi⟩)

lemma cyclic_orbit_poly_subspace_fractional_linear_scale_pow_sub_mul_div
    {M : Type*} [Field M] (g f : M) (hg : g ≠ 0) (i r : ℕ) (hi : i < r) :
    g ^ (r - 1) * (f / g) ^ i = f ^ i * g ^ (r - 1 - i) := by
  have : g ^ (r - 1) = g ^ (r - 1 - i) * g ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [div_pow, this]
  have hgi : g ^ i ≠ 0 := pow_ne_zero i hg
  rw [mul_assoc, mul_div_cancel₀ _ hgi]
  ring

lemma cyclic_orbit_poly_subspace_fractional_linear_scale_le
    {B M : Type*} [Field B] [Field M] [Algebra B M]
    (r : ℕ) (x y : M) (a b c d : B)
    (hcx : algebraMap B M c * x + algebraMap B M d ≠ 0)
    (hy : y = (algebraMap B M a * x + algebraMap B M b) / (algebraMap B M c * x + algebraMap B M d)) :
    (algebraMap B M c * x + algebraMap B M d) ^ (r - 1) • cyclic_orbit_poly_subspace B r y ≤
      cyclic_orbit_poly_subspace B r x := by
  dsimp [cyclic_orbit_poly_subspace, Submodule.pointwise_smul_def]
  rw [Submodule.map_span]
  rw [Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  dsimp [DistribSMul.toLinearMap]
  rw [hy]
  rw [cyclic_orbit_poly_subspace_fractional_linear_scale_pow_sub_mul_div _ _ hcx i.1 r i.2]
  have hp : aeval x ((C a * X + C b) ^ (i : ℕ) * (C c * X + C d) ^ (r - 1 - i) : B[X]) =
      (algebraMap B M a * x + algebraMap B M b) ^ (i : ℕ) * (algebraMap B M c * x + algebraMap B M d) ^ (r - 1 - i) := by
    simp only [map_mul, map_pow, map_add, aeval_C, aeval_X]
  rw [← hp]
  exact cyclic_orbit_poly_subspace_fractional_linear_scale_aeval_mem r x _
    (cyclic_orbit_poly_subspace_fractional_linear_scale_poly_deg a b c d i.1 r i.2)

lemma cyclic_orbit_poly_subspace_fractional_linear_scale_inv
    {B M : Type*} [Field B] [Field M] [Algebra B M]
    (a b c d : B) (x y : M) (hdet : a * d - b * c ≠ 0)
    (hcx : algebraMap B M c * x + algebraMap B M d ≠ 0)
    (hy : y = (algebraMap B M a * x + algebraMap B M b) / (algebraMap B M c * x + algebraMap B M d)) :
    algebraMap B M (-c) * y + algebraMap B M a ≠ 0 ∧
    x = (algebraMap B M d * y + algebraMap B M (-b)) / (algebraMap B M (-c) * y + algebraMap B M a) ∧
    (algebraMap B M (-c) * y + algebraMap B M a) * (algebraMap B M c * x + algebraMap B M d) =
      algebraMap B M (a * d - b * c) := by
  have hy' : y * (algebraMap B M c * x + algebraMap B M d) =
      algebraMap B M a * x + algebraMap B M b := by
    rw [hy, div_mul_cancel₀ _ hcx]
  have h_denom : (algebraMap B M (-c) * y + algebraMap B M a) * (algebraMap B M c * x + algebraMap B M d) =
      algebraMap B M (a * d - b * c) := by
    simp only [map_neg, map_sub, map_mul]
    calc (-algebraMap B M c * y + algebraMap B M a) * (algebraMap B M c * x + algebraMap B M d)
      _ = -algebraMap B M c * (y * (algebraMap B M c * x + algebraMap B M d)) +
            algebraMap B M a * (algebraMap B M c * x + algebraMap B M d) := by ring
      _ = -algebraMap B M c * (algebraMap B M a * x + algebraMap B M b) +
            algebraMap B M a * (algebraMap B M c * x + algebraMap B M d) := by rw [hy']
      _ = algebraMap B M a * algebraMap B M d - algebraMap B M b * algebraMap B M c := by ring
  have hdet_M : algebraMap B M (a * d - b * c) ≠ 0 := by
    intro h0
    have : a * d - b * c = 0 := (injective_iff_map_eq_zero (algebraMap B M)).mp (RingHom.injective _) _ h0
    exact hdet this
  have hdenom_ne : algebraMap B M (-c) * y + algebraMap B M a ≠ 0 := by
    intro h0
    have : algebraMap B M (a * d - b * c) = 0 := by rw [← h_denom, h0, zero_mul]
    exact hdet_M this
  refine ⟨hdenom_ne, ?_, h_denom⟩
  have h_num : (algebraMap B M d * y + algebraMap B M (-b)) * (algebraMap B M c * x + algebraMap B M d) =
      algebraMap B M (a * d - b * c) * x := by
    simp only [map_neg, map_sub, map_mul]
    calc (algebraMap B M d * y + -algebraMap B M b) * (algebraMap B M c * x + algebraMap B M d)
      _ = algebraMap B M d * (y * (algebraMap B M c * x + algebraMap B M d)) -
            algebraMap B M b * (algebraMap B M c * x + algebraMap B M d) := by ring
      _ = algebraMap B M d * (algebraMap B M a * x + algebraMap B M b) -
            algebraMap B M b * (algebraMap B M c * x + algebraMap B M d) := by rw [hy']
      _ = (algebraMap B M a * algebraMap B M d - algebraMap B M b * algebraMap B M c) * x := by ring
  have : (algebraMap B M d * y + algebraMap B M (-b)) / (algebraMap B M (-c) * y + algebraMap B M a) =
      ((algebraMap B M d * y + algebraMap B M (-b)) * (algebraMap B M c * x + algebraMap B M d)) /
        ((algebraMap B M (-c) * y + algebraMap B M a) * (algebraMap B M c * x + algebraMap B M d)) := by
    rw [mul_div_mul_right _ _ hcx]
  rw [this, h_denom, h_num, mul_div_cancel_left₀ _ hdet_M]

open Pointwise in
/-- Fractional linear scaling: (cx+d)^(r-1) • P_r(y) = P_r(x). -/
theorem cyclic_orbit_poly_subspace_fractional_linear_scale
    {B M : Type*} [Field B] [Field M] [Algebra B M]
    {r : ℕ} (hr : 2 ≤ r) {x y : M}
    (hx : 2 * r - 1 ≤ (minpoly B x).natDegree)
    (a b c d : B) (hdet : a * d - b * c ≠ 0)
    (hy : y = (algebraMap B M a * x + algebraMap B M b) / (algebraMap B M c * x + algebraMap B M d)) :
    (algebraMap B M c * x + algebraMap B M d) ^ (r - 1) • cyclic_orbit_poly_subspace B r y =
      cyclic_orbit_poly_subspace B r x := by
  have hdeg : 2 ≤ (minpoly B x).natDegree := by omega
  have hcx : algebraMap B M c * x + algebraMap B M d ≠ 0 :=
    cyclic_orbit_denom_ne_zero hdeg a b c d hdet
  have hle1 := cyclic_orbit_poly_subspace_fractional_linear_scale_le r x y a b c d hcx hy
  obtain ⟨hdenom_ne, hy_inv, hgh⟩ :=
    cyclic_orbit_poly_subspace_fractional_linear_scale_inv a b c d x y hdet hcx hy
  have hle2 := cyclic_orbit_poly_subspace_fractional_linear_scale_le r y x d (-b) (-c) a hdenom_ne hy_inv
  have hu : (a * d - b * c) ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hdet
  have h_scalar : (algebraMap B M ((a * d - b * c) ^ (r - 1))) • cyclic_orbit_poly_subspace B r x =
      cyclic_orbit_poly_subspace B r x := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (algebraMap B M ((a * d - b * c) ^ (r - 1))) * w ∈ cyclic_orbit_poly_subspace B r x
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hw
    · intro hz
      refine ⟨(algebraMap B M ((a * d - b * c) ^ (r - 1))⁻¹) * z, ?_, ?_⟩
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hz
      · change (algebraMap B M ((a * d - b * c) ^ (r - 1))) * ((algebraMap B M ((a * d - b * c) ^ (r - 1))⁻¹) * z) = z
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
  have h_comm : (algebraMap B M c * x + algebraMap B M d) * (algebraMap B M (-c) * y + algebraMap B M a) =
      algebraMap B M (a * d - b * c) := by
    rw [mul_comm, hgh]
  have h_prod : ((algebraMap B M c * x + algebraMap B M d) * (algebraMap B M (-c) * y + algebraMap B M a)) ^ (r - 1) =
      algebraMap B M ((a * d - b * c) ^ (r - 1)) := by
    rw [h_comm, map_pow]
  rw [mul_pow] at h_prod
  have h_assoc : ((algebraMap B M c * x + algebraMap B M d) ^ (r - 1) *
      (algebraMap B M (-c) * y + algebraMap B M a) ^ (r - 1)) • cyclic_orbit_poly_subspace B r x =
      (algebraMap B M c * x + algebraMap B M d) ^ (r - 1) •
        ((algebraMap B M (-c) * y + algebraMap B M a) ^ (r - 1) • cyclic_orbit_poly_subspace B r x) := by
    rw [mul_smul]
  have hle : cyclic_orbit_poly_subspace B r x ≤
      (algebraMap B M c * x + algebraMap B M d) ^ (r - 1) • cyclic_orbit_poly_subspace B r y := by
    rw [← h_scalar, ← h_prod, h_assoc]
    exact smul_le_smul_left _ hle2
  exact le_antisymm hle1 hle
