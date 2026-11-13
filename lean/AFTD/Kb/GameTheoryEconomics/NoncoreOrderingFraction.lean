import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarginalVector
import AFTD.Kb.GameTheoryEconomics.IsInCore

/-!
# noncore_ordering_fraction

Topic: general_equilibrium   Node: b8b5cf0aa5d0

Provenance: formalization of a published result. Source: arXiv:2611.16207, Section 1

For a cooperative game v : Finset α → ℝ on a finite type α with decidable equality, noncore_ordering_fraction v is the fraction of player ordering bijections e : Fin (Fintype.card α) ≃ α whose marginal worth vector marginal_vector v e does not belong to the core of v (¬ is_in_core v (marginal_vector v e)).
-/

/-- The probability that the marginal worth vector of a uniformly random player ordering is not in the core. -/
noncomputable def noncore_ordering_fraction {α : Type*} [DecidableEq α] [Fintype α] (v : Finset α → ℝ) : ℝ :=
  let _ : DecidablePred (fun (e : Fin (Fintype.card α) ≃ α) => ¬ is_in_core v (marginal_vector v e)) := Classical.decPred _
  ((Finset.univ.filter (fun (e : Fin (Fintype.card α) ≃ α) => ¬ is_in_core v (marginal_vector v e))).card : ℝ) /
    (Nat.factorial (Fintype.card α) : ℝ)
