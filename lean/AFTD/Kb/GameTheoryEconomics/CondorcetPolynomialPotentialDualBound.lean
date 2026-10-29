import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_polynomial_potential_dual_bound

Topic: social_choice   Node: 797316d86d74

Provenance: helper lemma. IN-341 supporting verification step for OP-19. Extends the subset-potential route from IN-339. Strict convention: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are construction and verification helpers, with no new election dimension bound or research advance claimed.

Let a finite signed subset polynomial be a sum of monomials indexed by a specified finite support. Suppose weighted rooted removal sets have the same natural incidence K on every supported monomial, and cover every selected challenger claim at least B times. If the polynomial satisfies all weighted local removal inequalities, B times the total challenger weight is at most K times its full-set value. This is an abstract certificate verifier, not a winning-set existence statement.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_polynomial_potential_dual_bound
    (C I J : Type*) [Fintype C] [DecidableEq C]
    [Fintype I] [Fintype J]
    (M : Finset (Finset C)) (c : Finset C → ℤ)
    (H : Finset C → ℤ)
    (hform : ∀ A, H A = ∑ T ∈ M, if T ⊆ A then c T else 0)
    (S : I → Finset C) (f : I → C) (w : I → ℕ)
    (A : J → Finset C) (a : J → C) (L : J → ℕ)
    (K B : ℕ) (ha : ∀ j, a j ∈ A j)
    (hinc : ∀ T ∈ M,
      (∑ j, if a j ∈ T ∧ T ⊆ A j then L j else 0) = K)
    (hcover : ∀ i,
      B ≤ ∑ j, if f i = a j ∧ S i ⊆ (A j).erase (a j) then L j else 0)
    (hstep : ∀ R : Finset C, ∀ b ∈ R,
      ((∑ i, if f i = b ∧ S i ⊆ R.erase b then w i else 0) : ℤ) +
        H (R.erase b) ≤ H R) :
    (B : ℤ) * (∑ i, (w i : ℤ)) ≤ (K : ℤ) * H univ := by
  classical
  have hmarg : ∀ j, H (A j) - H ((A j).erase (a j)) =
      ∑ T ∈ M, if a j ∈ T ∧ T ⊆ A j then c T else 0 := by
    intro j
    rw [hform, hform, ← sum_sub_distrib]
    apply sum_congr rfl
    intro T _
    by_cases hsub : T ⊆ A j
    · by_cases hmem : a j ∈ T
      · have hn : ¬ T ⊆ (A j).erase (a j) := by
          intro hh
          exact (mem_erase.mp (hh hmem)).1 rfl
        simp [hsub, hmem, hn]
      · have hs : T ⊆ (A j).erase (a j) := by
          intro b hb
          exact mem_erase.mpr ⟨by intro hh; subst b; exact hmem hb, hsub hb⟩
        simp [hsub, hmem, hs]
    · have hn : ¬ T ⊆ (A j).erase (a j) := by
        intro hh
        exact hsub (subset_trans hh (erase_subset _ _))
      simp [hsub, hn]
  have hsum : ∑ j, (L j : ℤ) * (H (A j) - H ((A j).erase (a j))) =
      (K : ℤ) * H univ := by
    simp_rw [hmarg, mul_sum]
    rw [sum_comm]
    have hterm : ∀ T ∈ M,
        (∑ j, (L j : ℤ) * (if a j ∈ T ∧ T ⊆ A j then c T else 0)) =
          (K : ℤ) * c T := by
      intro T hT
      have hc : (∑ j, if a j ∈ T ∧ T ⊆ A j then (L j : ℤ) else 0) = K := by
        exact_mod_cast hinc T hT
      rw [← hc, sum_mul]
      apply sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [sum_congr rfl hterm, ← mul_sum, hform]
    simp
  have hlower :
      (B : ℤ) * (∑ i, (w i : ℤ)) ≤
      ∑ j, (L j : ℤ) * ((∑ i,
        if f i = a j ∧ S i ⊆ (A j).erase (a j) then w i else 0) : ℤ) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_le_sum
    intro i _
    have hc : (B : ℤ) ≤ ∑ j,
        if f i = a j ∧ S i ⊆ (A j).erase (a j) then (L j : ℤ) else 0 := by
      exact_mod_cast hcover i
    have hh := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (w i) : (0 : ℤ) ≤ w i)
    simp_rw [sum_mul] at hh
    convert hh using 1
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp
  calc
    (B : ℤ) * (∑ i, (w i : ℤ)) ≤ _ := hlower
    _ ≤ ∑ j, (L j : ℤ) * (H (A j) - H ((A j).erase (a j))) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (L j))
      have hh := hstep (A j) (a j) (ha j)
      linarith
    _ = (K : ℤ) * H univ := hsum
