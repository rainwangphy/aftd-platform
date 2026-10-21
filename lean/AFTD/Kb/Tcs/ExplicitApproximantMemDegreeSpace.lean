import AFTD.Prelude
import AFTD.Kb.Tcs.ExplicitApproximant
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.TopCoefficient
import AFTD.Kb.Tcs.FullMonomial
import AFTD.Kb.Tcs.ParityCharacter
import AFTD.Kb.Tcs.Bit

/-!
# explicitApproximant_mem_degreeSpace

Topic: circuits   Node: 123b36a83ec8

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.14

For any Boolean function f : (Fin n → Bool) → Bool on n > 0 variables, the explicit approximant P_f belongs to degreeSpace (K := ℝ) (Fin n) (n - 1).
-/

open Finset

theorem explicitApproximant_prod_add_sub_top_mem {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) :
    (fun x : Fin n → Bool =>
      (∏ i : Fin n, (a i * bit (x i) + b i)) - (∏ i : Fin n, a i) * fullMonomial x) ∈
      degreeSpace ℝ (Fin n) (n - 1) := by
  have H : (fun x : Fin n → Bool =>
      (∏ i : Fin n, (a i * bit (x i) + b i)) - (∏ i : Fin n, a i) * fullMonomial x) =
      ∑ t ∈ univ.powerset.erase univ,
        ((∏ i ∈ t, a i) * (∏ i ∈ univ \ t, b i)) • (fun x => ∏ i ∈ t, bit (x i)) := by
    ext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hprod : ∏ i : Fin n, (a i * bit (x i) + b i) =
        (∏ i : Fin n, a i) * fullMonomial x +
        ∑ t ∈ univ.powerset.erase univ, (∏ i ∈ t, a i) * (∏ i ∈ univ \ t, b i) * (∏ i ∈ t, bit (x i)) := by
      rw [prod_add]
      have h_mem : univ ∈ (univ : Finset (Fin n)).powerset := mem_powerset_self univ
      rw [← add_sum_erase _ _ h_mem]
      congr 1
      · have : (univ : Finset (Fin n)) \ univ = ∅ := sdiff_self
        rw [this, prod_empty, mul_one, prod_mul_distrib]
        rfl
      · apply sum_congr rfl
        intro t _
        rw [prod_mul_distrib]
        ring
    rw [hprod]
    ring
  rw [H]
  apply Submodule.sum_mem
  intro t ht
  have ht_ne : t ≠ univ := (mem_erase.mp ht).1
  have ht_sub : t ⊂ univ := ssubset_univ_iff.mpr ht_ne
  have hcard : t.card < Fintype.card (Fin n) := card_lt_card ht_sub
  simp only [Fintype.card_fin] at hcard
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨t, by omega, rfl⟩

lemma explicitApproximant_parityCharacter_sub_top_mem {n : ℕ} (hn : 0 < n) :
    (fun x : Fin n → Bool => parityCharacter x - (2 : ℝ) ^ n * fullMonomial x) ∈
      degreeSpace ℝ (Fin n) (n - 1) := by
  have h := explicitApproximant_prod_add_sub_top_mem hn (fun _ => 2) (fun _ => -1)
  have hprod : (∏ i : Fin n, (2 : ℝ)) = (2 : ℝ) ^ n := by simp
  have heq : (fun x : Fin n → Bool => parityCharacter x - (2 : ℝ) ^ n * fullMonomial x) =
      (fun x => (∏ i : Fin n, ((2 : ℝ) * bit (x i) + -1)) - (∏ i : Fin n, (2 : ℝ)) * fullMonomial x) := by
    ext x
    congr 1
    · dsimp [parityCharacter]
      apply prod_congr rfl
      intro i _
      cases x i <;> simp [bit] <;> norm_num
    · rw [hprod]
  rw [heq]
  exact h

lemma explicitApproximant_delta_sub_top_mem {n : ℕ} (hn : 0 < n) (y : Fin n → Bool) :
    (fun x : Fin n → Bool => (if x = y then (1 : ℝ) else 0) - parityCharacter y * fullMonomial x) ∈
      degreeSpace ℝ (Fin n) (n - 1) := by
  have h := explicitApproximant_prod_add_sub_top_mem hn
    (fun i => if y i = true then 1 else -1) (fun i => if y i = true then 0 else 1)
  have heq : (fun x : Fin n → Bool => (if x = y then (1 : ℝ) else 0) - parityCharacter y * fullMonomial x) =
      (fun x => (∏ i : Fin n, ((if y i = true then (1:ℝ) else -1) * bit (x i) + (if y i = true then 0 else 1))) -
        (∏ i : Fin n, (if y i = true then (1:ℝ) else -1)) * fullMonomial x) := by
    ext x
    have Hfactor : ∀ i : Fin n,
        (if x i = y i then (1 : ℝ) else 0) =
        ((if y i = true then 1 else -1) * bit (x i) + (if y i = true then 0 else 1)) := by
      intro i
      cases x i <;> cases y i <;> simp [bit]
    have Hprod : (if x = y then (1 : ℝ) else 0) = ∏ i : Fin n, (if x i = y i then (1 : ℝ) else 0) := by
      split_ifs with hxy
      · subst hxy; simp
      · have : ∃ i : Fin n, x i ≠ y i := by
          contrapose! hxy
          ext i
          exact hxy i
        rcases this with ⟨i, hi⟩
        symm
        exact prod_eq_zero (mem_univ i) (if_neg hi)
    dsimp [parityCharacter]
    rw [Hprod, prod_congr rfl (fun i _ => Hfactor i)]
  rw [heq]
  exact h

lemma explicitApproximant_function_sub_top_mem {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    (fun x : Fin n → Bool => (if f x = true then (1 : ℝ) else 0) - (topCoefficient f : ℝ) * fullMonomial x) ∈
      degreeSpace ℝ (Fin n) (n - 1) := by
  have H : (fun x : Fin n → Bool => (if f x = true then (1 : ℝ) else 0) - (topCoefficient f : ℝ) * fullMonomial x) =
      ∑ y, (if f y = true then (1 : ℝ) else 0) •
        (fun x => (if x = y then 1 else 0) - parityCharacter y * fullMonomial x) := by
    ext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have H1 : (∑ y, (if f y = true then (1 : ℝ) else 0) * (if x = y then 1 else 0)) = (if f x = true then 1 else 0) := by
      rw [sum_eq_single x]
      · simp
      · intro y _ hy
        have : ¬x = y := ne_comm.mp hy
        rw [if_neg this, mul_zero]
      · intro h
        exact False.elim (h (mem_univ x))
    have H2 : (∑ y, (if f y = true then (1 : ℝ) else 0) * (parityCharacter y * fullMonomial x)) =
        (topCoefficient f : ℝ) * fullMonomial x := by
      dsimp [topCoefficient, parityCharacter]
      push_cast
      rw [sum_mul]
      apply sum_congr rfl
      intro y _
      split_ifs with h <;> ring
    rw [← H1, ← H2, ← sum_sub_distrib]
    apply sum_congr rfl
    intro y _
    ring
  rw [H]
  apply Submodule.sum_mem
  intro y _
  apply Submodule.smul_mem
  exact explicitApproximant_delta_sub_top_mem hn y

/-- The explicit approximant has degree at most n - 1. -/
theorem explicitApproximant_mem_degreeSpace {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) :
    explicitApproximant f ∈ degreeSpace (K := ℝ) (Fin n) (n - 1) := by
  have h1 := explicitApproximant_function_sub_top_mem hn f
  have h2 := explicitApproximant_parityCharacter_sub_top_mem hn
  have hdiv : topCoefficient f = 2 * (topCoefficient f / 2) + topCoefficient f % 2 := by omega
  have hdivR : (topCoefficient f : ℝ) = 2 * ((topCoefficient f / 2 : ℤ) : ℝ) + ((topCoefficient f % 2 : ℤ) : ℝ) := by
    exact_mod_cast hdiv
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := pow_succ 2 n
  have he2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have Heq : explicitApproximant f =
      (1 / 2 : ℝ) • (fun x => (if f x = true then 1 else 0) - (topCoefficient f : ℝ) * fullMonomial x) -
      (((topCoefficient f % 2 : ℤ) : ℝ) / 2 ^ (n + 1)) •
        (fun x => parityCharacter x - (2 : ℝ) ^ n * fullMonomial x) := by
    ext x
    dsimp [explicitApproximant]
    rw [hdivR, hpow]
    have hcalc : ∀ (a b c d e p : ℝ), e ≠ 0 →
      a / 2 - b * d - c * p / (e * 2) = (1 / 2) * (a - (2 * b + c) * d) - (c / (e * 2)) * (p - e * d) := by
      intro a b c d e p he
      have : c / (e * 2) * (p - e * d) = c * p / (e * 2) - c * e * d / (e * 2) := by ring
      rw [this]
      have he_cancel : c * e * d / (e * 2) = c * d / 2 := by
        calc c * e * d / (e * 2) = (c * d) * e / (2 * e) := by ring
        _ = c * d / 2 := mul_div_mul_right (c * d) 2 he
      rw [he_cancel]
      ring
    exact hcalc (if f x = true then 1 else 0) ((topCoefficient f / 2 : ℤ) : ℝ)
      ((topCoefficient f % 2 : ℤ) : ℝ) (fullMonomial x) (2 ^ n) (parityCharacter x) he2n
  rw [Heq]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
