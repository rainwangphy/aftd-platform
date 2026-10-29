import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_subset_potential_of_cardinality_slack

Topic: social_choice   Node: b76a32a0c93d

Provenance: helper lemma. IN-341 supporting verification step for OP-19. Extends the subset-potential route from IN-339. Strict convention: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are construction and verification helpers, with no new election dimension bound or research advance claimed.

For a finite family of weighted challenger claims, suppose an integer potential has local removal deficit bounded by an arbitrary integer delta(k), where k is the cardinality after removal. There exists a natural-valued valid subset potential whose full-set value is the original full value plus the sum of delta(k) for k below the candidate count, minus the original empty-set value. The increments may be negative. No existence of such small deficits for arbitrary selectors is asserted.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_subset_potential_of_cardinality_slack
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) (H : Finset (Fin m) → ℤ) (δ : ℕ → ℤ)
    (hslack : ∀ A : Finset (Fin m), ∀ a ∈ A,
      ((∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) : ℤ) +
        H (A.erase a) ≤ H A + δ ((A.erase a).card)) :
    ∃ K : Finset (Fin m) → ℕ,
      (∀ A : Finset (Fin m), ∀ a ∈ A,
        (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) +
          K (A.erase a) ≤ K A) ∧
      ((K univ : ℕ) : ℤ) = H univ + (∑ k ∈ range m, δ k) - H ∅ := by
  classical
  let J : Finset (Fin m) → ℤ := fun A =>
    H A + (∑ k ∈ range A.card, δ k) - H ∅
  have hlocal : ∀ A : Finset (Fin m), ∀ a ∈ A,
      ((∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) : ℤ) +
        J (A.erase a) ≤ J A := by
    intro A a ha
    have hcard : A.card = (A.erase a).card + 1 := (card_erase_add_one ha).symm
    have hs := hslack A a ha
    dsimp only [J]
    rw [hcard, sum_range_succ]
    omega
  have hnonneg : ∀ A : Finset (Fin m), 0 ≤ J A := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [J]
    | @insert a A ha ih =>
      have hl := hlocal (insert a A) a (mem_insert_self a A)
      have he : (insert a A).erase a = A := erase_insert ha
      rw [he] at hl
      have hn : (0 : ℤ) ≤
          (∑ i, if f i = a ∧ S i ⊆ A then (w i : ℤ) else 0) := by positivity
      omega
  let K : Finset (Fin m) → ℕ := fun A => (J A).toNat
  have hcast : ∀ A, (K A : ℤ) = J A := fun A => Int.toNat_of_nonneg (hnonneg A)
  refine ⟨K, ?_, ?_⟩
  · intro A a ha
    have hl := hlocal A a ha
    rw [← hcast (A.erase a), ← hcast A] at hl
    exact_mod_cast hl
  · rw [hcast]
    simp only [J, card_univ, Fintype.card_fin]
