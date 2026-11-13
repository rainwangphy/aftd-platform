import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ug

/-!
# UgCount

Topic: general_equilibrium   Node: 6ada63b8f77d

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The number of player orderings that satisfy the good-ordering event Ug for at least one group index g.
-/

/-- Number of orderings satisfying Ug for some group; its ratio to n! lower-bounds the non-core ordering fraction. -/
noncomputable def UgCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Fin (Fintype.card (Fin n)) ≃ Fin n => ∃ g, Ug e g)).card
