import AFTD.Prelude

/-!
# violates_supermodularity

Topic: general_equilibrium   Node: cc71db3dd385

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_sharp_two_log_over_n

The pair (S,T) violates supermodularity for the game v: v(S) + v(T) > v(S ∪ T) + v(S ∩ T).
-/

/-- The unordered coalition pair (S, T) violates the supermodularity inequality for v. -/
def violates_supermodularity {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (S T : Finset α) : Prop := v (S ∪ T) + v (S ∩ T) < v S + v T
