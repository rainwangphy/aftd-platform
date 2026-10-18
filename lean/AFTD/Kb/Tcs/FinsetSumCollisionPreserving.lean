import AFTD.Prelude

/-!
# finset_sum_collision_preserving

Topic: combinatorics   Node: a4964933ac1f

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

A rational-valued function x on A is collision-preserving if it satisfies every additive collision: x a + x b = x c + x d whenever a + b = c + d with a, b, c, d ∈ A.
-/

/-- Rational collision-preserving weight on A: additive relations in A force the same relations among the weights. -/
def finset_sum_collision_preserving {G : Type*} [AddCommMonoid G] (A : Finset G) (x : G → ℚ) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → x a + x b = x c + x d
