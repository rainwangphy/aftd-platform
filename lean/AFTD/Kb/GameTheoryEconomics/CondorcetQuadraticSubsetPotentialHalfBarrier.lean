import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_quadratic_subset_potential_half_barrier

Topic: social_choice   Node: 5bb66e5b77aa

Provenance: helper lemma. IN-339 supporting method lemma for the uniform subset-potential route to OP-19. Strict winning-set convention from Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015); related selector formulation arXiv:2604.19851v2. No new election bound or research advance is asserted.

Let an integer-valued subset potential be represented by arbitrary integer vertex coefficients and ordered-pair coefficients with zero diagonal. For any outside-challenger selector and nonnegative integer claim weights, if all candidate-removal gain inequalities hold, the total claim weight is at most twice the full-set potential. Thus this quadratic representation cannot supply a strict half-weight ordering certificate. This limits a proof ansatz, not the winning-triple conjecture.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_quadratic_subset_potential_half_barrier
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) (H : Finset (Fin m) → ℤ)
    (α : Fin m → ℤ) (β : Fin m → Fin m → ℤ)
    (hform : ∀ A, H A = (∑ a ∈ A, α a) + ∑ a ∈ A, ∑ b ∈ A, β a b)
    (hdiag : ∀ a, β a a = 0) (houtside : ∀ i, f i ∉ S i)
    (hstep : ∀ A : Finset (Fin m), ∀ a ∈ A,
      ((∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) : ℤ) +
        H (A.erase a) ≤ H A) :
    ((∑ i, w i) : ℤ) ≤ 2 * H univ := by
  classical
  have hα : ∀ a, 0 ≤ α a := by
    intro a
    have hl := hstep {a} a (by simp)
    simp only [erase_singleton] at hl
    rw [hform ∅, hform {a}] at hl
    simp only [erase_singleton, sum_empty, sum_singleton, hdiag, add_zero] at hl
    exact le_trans (by positivity) hl
  have hfull : ∀ a : Fin m,
      H univ = H (univ.erase a) + α a + (∑ b, β a b) + ∑ b, β b a := by
    intro a
    have hαsum := sum_erase_add univ α (mem_univ a)
    have hrows := sum_erase_add univ (fun x => ∑ y, β x y) (mem_univ a)
    have hcols := sum_erase_add univ (fun x => β x a) (mem_univ a)
    have hinner : (∑ x ∈ univ.erase a, ∑ y, β x y) =
        (∑ x ∈ univ.erase a, ∑ y ∈ univ.erase a, β x y) +
          ∑ x ∈ univ.erase a, β x a := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      exact (sum_erase_add univ (β x) (mem_univ a)).symm
    rw [hdiag] at hcols
    rw [hform univ, hform (univ.erase a)]
    linarith
  have hgains : (∑ a : Fin m,
      ((∑ i, if f i = a ∧ S i ⊆ (univ : Finset (Fin m)).erase a then w i else 0) : ℤ)) =
        ((∑ i, w i) : ℤ) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    have ht : S i ⊆ (univ : Finset (Fin m)).erase (f i) := by
      intro b hb
      exact mem_erase.mpr ⟨by intro heq; subst b; exact houtside i hb, mem_univ b⟩
    have heq : ∀ a, (if f i = a ∧ S i ⊆ (univ : Finset (Fin m)).erase a
        then (w i : ℤ) else 0) = if f i = a then (w i : ℤ) else 0 := by
      intro a
      by_cases ha : f i = a
      · subst a
        simp only [ht, and_true, if_true, eq_self_iff_true]
      · simp only [ha, false_and, if_false]
    simp_rw [heq]
    simp
  have hsum :
      (∑ a : Fin m,
        ((∑ i, if f i = a ∧ S i ⊆ (univ : Finset (Fin m)).erase a then w i else 0) : ℤ)) ≤
      (∑ a : Fin m, (α a + (∑ b, β a b) + (∑ b, β b a))) := by
    apply sum_le_sum
    intro a _
    have hl := hstep univ a (mem_univ a)
    have he := hfull a
    linarith
  rw [hgains] at hsum
  have hswap : (∑ a, ∑ b, β b a) = ∑ a, ∑ b, β a b := sum_comm
  simp only [sum_add_distrib] at hsum
  rw [hswap] at hsum
  have hnonneg : 0 ≤ ∑ a, α a := sum_nonneg (fun a _ => hα a)
  rw [hform univ]
  linarith
