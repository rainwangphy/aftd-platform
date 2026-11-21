import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChorePrefixBundle
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# has_finite_tef1_factor

Topic: fair_division   Node: 2975a3aada4c

Provenance: formalization of a published result. Source: arXiv:2611.25892, Lemma 2.3

An allocation π has finite temporal EF1 factor if for every prefix round t and all distinct agents i and j, whenever agent i has strictly positive residual cost at round t, agent j's prefix bundle has strictly positive cost under agent i's cost function.
-/

/-- An allocation has finite temporal EF1 factor if whenever an agent has positive residual cost at round t, every other agent's prefix bundle has positive cost. -/
def has_finite_tef1_factor (n m : ℕ) (d : Fin n → Fin m → ℝ) (π : Fin m → Fin n) : Prop := ∀ (t : Fin m) (i j : Fin n), i ≠ j →
    0 < additive_valuation (d i) (chore_prefix_bundle π t i) - (chore_prefix_bundle π t i).fold max 0 (d i) →
    0 < additive_valuation (d i) (chore_prefix_bundle π t j)
