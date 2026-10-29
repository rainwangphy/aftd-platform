import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_subset_potential_of_integer_slack

Topic: social_choice   Node: 9c003c7bf778

Provenance: helper lemma. IN-339 supporting method lemma for the uniform subset-potential route to OP-19. Strict winning-set convention from Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015); related selector formulation arXiv:2604.19851v2. No new election bound or research advance is asserted.

For any family of challenger claims with nonnegative integer weights and an integer-valued subset function, suppose every candidate-removal inequality has deficit at most a fixed natural number delta. There is a natural-valued subset potential satisfying all the exact removal inequalities whose full-set value equals the original full-set value plus delta times the number of candidates minus the original empty-set value. This repairs verified integer rounding deficits; it does not assert a strict half bound.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_subset_potential_of_integer_slack
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) (H : Finset (Fin m) → ℤ) (δ : ℕ)
    (hslack : ∀ A : Finset (Fin m), ∀ a ∈ A,
      ((∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) : ℤ) +
        H (A.erase a) ≤ H A + δ) :
    ∃ K : Finset (Fin m) → ℕ,
      (∀ A : Finset (Fin m), ∀ a ∈ A,
        (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) +
          K (A.erase a) ≤ K A) ∧
      ((K univ : ℕ) : ℤ) = H univ + (δ : ℤ) * m - H ∅ := by
  classical
  let J : Finset (Fin m) → ℤ := fun A => H A + (δ : ℤ) * A.card - H ∅
  have hlocal : ∀ A : Finset (Fin m), ∀ a ∈ A,
      ((∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) : ℤ) +
        J (A.erase a) ≤ J A := by
    intro A a ha
    have hcard : (A.card : ℤ) = ((A.erase a).card : ℤ) + 1 := by
      exact_mod_cast (card_erase_add_one ha).symm
    have hs := hslack A a ha
    dsimp only [J]
    rw [hcard]
    nlinarith
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
  have hcast : ∀ A, (K A : ℤ) = J A := by
    intro A
    exact Int.toNat_of_nonneg (hnonneg A)
  refine ⟨K, ?_, ?_⟩
  · intro A a ha
    have hl := hlocal A a ha
    rw [← hcast (A.erase a), ← hcast A] at hl
    exact_mod_cast hl
  · rw [hcast]
    simp only [J, card_univ, Fintype.card_fin]
