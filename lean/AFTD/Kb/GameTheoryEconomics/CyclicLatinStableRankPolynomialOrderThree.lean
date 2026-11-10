import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankPolynomial
import AFTD.Kb.GameTheoryEconomics.IsStableMatching
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankMatching
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankMatchingIsStable
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankSum
import AFTD.Kb.GameTheoryEconomics.CyclicLatinMarket

/-!
# cyclic_latin_stable_rank_polynomial_order_three

Topic: matching_markets   Node: 0fa1f4a5e861

Provenance: original. Related work: folklore

For n = 3, any two ordering bijections a and b from Fin 3 to ZMod 3 have identical stable-matching rank polynomials: cyclic_latin_rank_polynomial 3 a = cyclic_latin_rank_polynomial 3 b.
-/

instance cyclic_latin_stable_rank_polynomial_order_three_dec_block
    (a : Fin 3 ≃ ZMod 3) (m : ZMod 3) (w : ZMod 3) (μ : Equiv.Perm (ZMod 3)) :
    Decidable (is_blocking_pair (cyclic_latin_market 3 a) μ m w) := by
  dsimp [is_blocking_pair, cyclic_latin_market]
  infer_instance

instance cyclic_latin_stable_rank_polynomial_order_three_dec_stable
    (a : Fin 3 ≃ ZMod 3) (μ : Equiv.Perm (ZMod 3)) :
    Decidable (is_stable_matching (cyclic_latin_market 3 a) μ) := by
  dsimp [is_stable_matching]
  infer_instance

theorem cyclic_latin_stable_rank_polynomial_order_three_is_stable_iff
    (a : Fin 3 ≃ ZMod 3) (π : Equiv.Perm (ZMod 3)) :
    is_stable_matching (cyclic_latin_market 3 a) π ↔
      ∃ r : Fin 3, π = cyclic_latin_rank_matching 3 a r := by
  revert a π
  decide

theorem cyclic_latin_stable_rank_polynomial_order_three_rank_sum_matching
    (a : Fin 3 ≃ ZMod 3) (r : Fin 3) :
    cyclic_latin_rank_sum 3 a (cyclic_latin_rank_matching 3 a r) = 3 * (r : ℕ) := by
  revert a r
  decide

theorem cyclic_latin_stable_rank_polynomial_order_three_rank_matching_inj
    (a : Fin 3 ≃ ZMod 3) (r₁ r₂ : Fin 3) :
    cyclic_latin_rank_matching 3 a r₁ = cyclic_latin_rank_matching 3 a r₂ ↔ r₁ = r₂ := by
  revert a r₁ r₂
  decide

lemma cyclic_latin_stable_rank_polynomial_order_three_poly_eq (a : Fin 3 ≃ ZMod 3) :
    cyclic_latin_rank_polynomial 3 a = ∑ r : Fin 3, (Polynomial.X : Polynomial ℤ) ^ (3 * (r : ℕ)) := by
  unfold cyclic_latin_rank_polynomial
  let f : Equiv.Perm (ZMod 3) → Polynomial ℤ := fun π =>
    @ite (Polynomial ℤ) (is_stable_matching (cyclic_latin_market 3 a) π)
      (Classical.propDecidable _)
      ((Polynomial.X : Polynomial ℤ) ^ (cyclic_latin_rank_sum 3 a π))
      0
  change (∑ π : Equiv.Perm (ZMod 3), f π) = _
  let S := Finset.univ.image (cyclic_latin_rank_matching 3 a)
  have h_sub : S ⊆ Finset.univ := Finset.subset_univ _
  have h_zero : ∀ π ∈ Finset.univ, π ∉ S → f π = 0 := by
    intro π _ hπ
    have h_not_stable : ¬ is_stable_matching (cyclic_latin_market 3 a) π := by
      intro hst
      rw [cyclic_latin_stable_rank_polynomial_order_three_is_stable_iff] at hst
      rcases hst with ⟨r, hr⟩
      apply hπ
      rw [Finset.mem_image]
      exact ⟨r, Finset.mem_univ _, hr.symm⟩
    dsimp [f]
    rw [if_neg h_not_stable]
  have h_step1 : (∑ π : Equiv.Perm (ZMod 3), f π) = ∑ π ∈ S, f π := (Finset.sum_subset h_sub h_zero).symm
  rw [h_step1]
  have h_inj : Set.InjOn (cyclic_latin_rank_matching 3 a) ↑(Finset.univ : Finset (Fin 3)) := by
    intro r₁ _ r₂ _ hr
    rwa [cyclic_latin_stable_rank_polynomial_order_three_rank_matching_inj] at hr
  rw [Finset.sum_image h_inj]
  apply Finset.sum_congr rfl
  intro r _
  dsimp [f]
  have hst : is_stable_matching (cyclic_latin_market 3 a) (cyclic_latin_rank_matching 3 a r) :=
    cyclic_latin_rank_matching_is_stable 3 a r
  rw [if_pos hst, cyclic_latin_stable_rank_polynomial_order_three_rank_sum_matching]

/-- OP-1351 holds for n = 3: all orderings have identical stable-matching rank polynomial. -/
theorem cyclic_latin_stable_rank_polynomial_order_three (a b : Fin 3 ≃ ZMod 3) :
    cyclic_latin_rank_polynomial 3 a = cyclic_latin_rank_polynomial 3 b := by
  rw [cyclic_latin_stable_rank_polynomial_order_three_poly_eq a,
      cyclic_latin_stable_rank_polynomial_order_three_poly_eq b]
