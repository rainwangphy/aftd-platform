import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetSumCollisionPreservingConstOfMinimal
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetSumCollisionPreserving

/-!
# nus_int_collision_preserving_const_of_minimal

Topic: combinatorics   Node: 7ebb83062fd9

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

If A is NUS, no proper subset of A is NUS, and x : G → ℤ is constant across additive collisions on A, then x is constant on A.
-/

/-- Integer form of the rational rank statement: on an inclusion-minimal NUS set every integer-valued collision-preserving weight is constant. -/
theorem nus_int_collision_preserving_const_of_minimal {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {A : Finset G} (hA : finset_has_no_unique_sums A)
    (hmin : ∀ B : Finset G, B ⊂ A → ¬ finset_has_no_unique_sums B)
    {x : G → ℤ}
    (hx : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → x a + x b = x c + x d) :
    ∀ a ∈ A, ∀ b ∈ A, x a = x b := by
  have hxQ : finset_sum_collision_preserving A (fun a => (x a : ℚ)) := by
    intro a ha b hb c hc d hd habcd
    dsimp
    norm_cast
    exact hx a ha b hb c hc d hd habcd
  intro a ha b hb
  have h := finset_sum_collision_preserving_const_of_minimal hA hmin hxQ a ha b hb
  exact_mod_cast h
