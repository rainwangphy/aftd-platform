import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetContainsKAp

/-!
# random_deletion_inequality_k_ap

Topic: combinatorics   Node: d046249556b8

Provenance: formalization of a published result. Source: arXiv:2610.26243 Lemma 2.2 -- Families that intersect in an arithmetic progression

Let 𝒜 and 𝒞 be families in Finset (Finset (Fin n)) such that 𝒜 is an up-set, 𝒞 is a down-set, and for every A ∈ 𝒜 and C ∈ 𝒞, the difference A \ C contains a k-term arithmetic progression in Fin n. For each X : Finset (Fin n), let p X : Finset (Fin n) → ℝ be a probability distribution supported on subsets Z ⊆ X with ∑ Z ∈ X.powerset, p X Z = 1. Define W X = ∑ Z ∈ X.powerset, p X Z * (if X \ Z ∈ 𝒞 then 1 else 0). If W X > 0 for all X, then ((𝒜.card : ℝ) / 2 ^ n) * ((𝒞.card : ℝ) / 2 ^ n) ≤ (1 / (2 ^ n : ℝ)) * ∑ X : Finset (Fin n), (((𝒞.card : ℝ) / 2 ^ n) / W X) * ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0).
-/

open scoped BigOperators Classical in
/-- Random-deletion inequality for the product density of k-AP cross-intersecting families (arXiv:2610.26243, Lemma 2.2). -/
theorem random_deletion_inequality_k_ap
    (n k : ℕ)
    (𝒜 𝒞 : Finset (Finset (Fin n)))
    (hA_upper : IsUpperSet (𝒜 : Set (Finset (Fin n))))
    (hC_lower : IsLowerSet (𝒞 : Set (Finset (Fin n))))
    (h_cross : ∀ A ∈ 𝒜, ∀ C ∈ 𝒞, finset_contains_k_ap n k (A \ C))
    (p : Finset (Fin n) → Finset (Fin n) → ℝ)
    (hp_nonneg : ∀ X Z, 0 ≤ p X Z)
    (hp_supp : ∀ X Z, p X Z ≠ 0 → Z ⊆ X)
    (hp_sum : ∀ X, ∑ Z ∈ X.powerset, p X Z = 1)
    (W : Finset (Fin n) → ℝ)
    (hW : ∀ X, W X = ∑ Z ∈ X.powerset, p X Z * (if X \ Z ∈ 𝒞 then 1 else 0))
    (hW_pos : ∀ X, 0 < W X) :
    ((𝒜.card : ℝ) / 2 ^ n) * ((𝒞.card : ℝ) / 2 ^ n) ≤
      (1 / (2 ^ n : ℝ)) * ∑ X : Finset (Fin n),
        (((𝒞.card : ℝ) / 2 ^ n) / W X) *
          ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := by
  have h_le_Z : ∀ (X Z : Finset (Fin n)), Z ∈ X.powerset →
      (if X ∈ 𝒜 then (1 : ℝ) else 0) * (p X Z * (if X \ Z ∈ 𝒞 then 1 else 0)) ≤
        p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := by
    intro X Z hZ
    have hZ_sub : Z ⊆ X := Finset.mem_powerset.mp hZ
    have h_ineq : (if X ∈ 𝒜 then (1 : ℝ) else 0) * (if X \ Z ∈ 𝒞 then 1 else 0) ≤
        (if finset_contains_k_ap n k Z then 1 else 0) := by
      by_cases hX : X ∈ 𝒜
      · by_cases hC : X \ Z ∈ 𝒞
        · have h_ap : finset_contains_k_ap n k Z := by
            have := h_cross X hX (X \ Z) hC
            rwa [Finset.sdiff_sdiff_eq_self hZ_sub] at this
          simp [hX, hC, h_ap]
        · simp only [hX, hC, ↓reduceIte, mul_zero]
          split_ifs <;> linarith
      · simp only [hX, ↓reduceIte, zero_mul]
        split_ifs <;> linarith
    have hp := hp_nonneg X Z
    calc
      (if X ∈ 𝒜 then (1 : ℝ) else 0) * (p X Z * (if X \ Z ∈ 𝒞 then 1 else 0))
      _ = p X Z * ((if X ∈ 𝒜 then (1 : ℝ) else 0) * (if X \ Z ∈ 𝒞 then 1 else 0)) := by ring
      _ ≤ p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := mul_le_mul_of_nonneg_left h_ineq hp

  have h_le_X : ∀ X : Finset (Fin n),
      (if X ∈ 𝒜 then (1 : ℝ) else 0) * ((𝒞.card : ℝ) / 2 ^ n) ≤
        (((𝒞.card : ℝ) / 2 ^ n) / W X) *
          ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := by
    intro X
    have h_sum_le : (if X ∈ 𝒜 then (1 : ℝ) else 0) * W X ≤
        ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := by
      rw [hW X, Finset.mul_sum]
      exact Finset.sum_le_sum (h_le_Z X)
    have hW_pos_X := hW_pos X
    have h_div : (if X ∈ 𝒜 then (1 : ℝ) else 0) ≤
        (∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0)) / W X := by
      rw [le_div_iff₀ hW_pos_X]
      linarith
    have hC_nonneg : 0 ≤ (𝒞.card : ℝ) / 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_right h_div hC_nonneg
    calc
      (if X ∈ 𝒜 then (1 : ℝ) else 0) * ((𝒞.card : ℝ) / 2 ^ n)
      _ ≤ ((∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0)) / W X) *
            ((𝒞.card : ℝ) / 2 ^ n) := this
      _ = (((𝒞.card : ℝ) / 2 ^ n) / W X) *
            ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := by ring

  have h_sum_all : ∑ X : Finset (Fin n), (if X ∈ 𝒜 then (1 : ℝ) else 0) * ((𝒞.card : ℝ) / 2 ^ n) ≤
      ∑ X : Finset (Fin n), (((𝒞.card : ℝ) / 2 ^ n) / W X) *
        ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) :=
    Finset.sum_le_sum (fun X _ => h_le_X X)
  rw [← Finset.sum_mul] at h_sum_all
  have h_sum_A : ∑ X : Finset (Fin n), (if X ∈ 𝒜 then (1 : ℝ) else 0) = (𝒜.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [h_sum_A] at h_sum_all
  have h_pow_pos : 0 ≤ (1 : ℝ) / 2 ^ n := by positivity
  have h_final := mul_le_mul_of_nonneg_left h_sum_all h_pow_pos
  calc
    ((𝒜.card : ℝ) / 2 ^ n) * ((𝒞.card : ℝ) / 2 ^ n)
    _ = (1 / (2 ^ n : ℝ)) * ((𝒜.card : ℝ) * ((𝒞.card : ℝ) / 2 ^ n)) := by ring
    _ ≤ (1 / (2 ^ n : ℝ)) * ∑ X : Finset (Fin n),
          (((𝒞.card : ℝ) / 2 ^ n) / W X) *
            ∑ Z ∈ X.powerset, p X Z * (if finset_contains_k_ap n k Z then 1 else 0) := h_final
