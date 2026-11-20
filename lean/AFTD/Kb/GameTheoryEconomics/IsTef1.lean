import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChorePrefixBundle
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_tef1

Topic: fair_division   Node: 567f5770ab37

Provenance: formalization of a published result. Source: arXiv:2611.25892 Def. 2.1

An allocation π : Fin m → Fin n of m chores to n agents is temporal EF1 (TEF1) with respect to additive costs d : Fin n → Fin m → ℝ if for every round t : Fin m and all distinct agents i j : Fin n with i ≠ j, the additive valuation of agent i's prefix bundle chore_prefix_bundle π t i under d i is at most that of agent j's prefix bundle chore_prefix_bundle π t j, or there exists some chore c ∈ chore_prefix_bundle π t i such that subtracting d i c from the additive valuation of i's prefix bundle makes it at most the additive valuation of j's prefix bundle.
-/

/-- Temporal EF1 (TEF1) for indivisible chores with additive costs. -/
def is_tef1 (n m : ℕ) (d : Fin n → Fin m → ℝ) (π : Fin m → Fin n) : Prop := ∀ (t : Fin m) (i j : Fin n), i ≠ j →
    additive_valuation (d i) (chore_prefix_bundle π t i) ≤ additive_valuation (d i) (chore_prefix_bundle π t j) ∨
    ∃ c ∈ chore_prefix_bundle π t i,
      additive_valuation (d i) (chore_prefix_bundle π t i) - d i c ≤ additive_valuation (d i) (chore_prefix_bundle π t j)
