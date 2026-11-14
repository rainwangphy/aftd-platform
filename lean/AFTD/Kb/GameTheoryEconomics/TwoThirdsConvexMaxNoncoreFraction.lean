import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.NoncoreOrderingFraction

/-!
# two_thirds_convex_max_noncore_fraction

Topic: general_equilibrium   Node: 4ede50275615

Provenance: formalization of a published result. Source: OP-1671

For each n, two_thirds_convex_max_noncore_fraction n is the supremum over all 2/3-convex cooperative games v on Fin n with v(∅) = 0 of the fraction of player orderings whose marginal worth vector lies outside the core.
-/

/-- The supremum over all 2/3-convex TU games on Fin n vanishing at ∅ of the fraction of orderings outside the core. -/
noncomputable def two_thirds_convex_max_noncore_fraction (n : ℕ) : ℝ := sSup { noncore_ordering_fraction v | (v : Finset (Fin n) → ℝ) (_ : v ∅ = 0) (_ : is_two_thirds_convex v) }
