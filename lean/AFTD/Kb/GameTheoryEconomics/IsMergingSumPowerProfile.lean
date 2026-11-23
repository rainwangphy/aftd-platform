import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerRelation
import AFTD.Kb.GameTheoryEconomics.PowerProfile

/-!
# is_merging_sum_power_profile

Topic: social_choice   Node: 52c49b55efab

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 4(2)

A profile π is a merging sum of two profiles π₁ and π₂ of equal cardinality if their elements can be ordered as lists such that each element of π is a merging sum of the corresponding pair from π₁ and π₂.
-/

/-- A profile is a merging sum of two profiles of the same cardinality if its elements are merging sums of paired power relations. -/
def is_merging_sum_power_profile {X : Type*} (π π₁ π₂ : PowerProfile X) : Prop := ∃ (l l₁ l₂ : List (PowerRelation X)),
    π = ↑l ∧ π₁ = ↑l₁ ∧ π₂ = ↑l₂ ∧
    l₁.length = l₂.length ∧ l.length = l₁.length ∧
    ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length) (h : i < l.length),
      is_merging_sum_power_relation (l[i]'h) (l₁[i]'h₁) (l₂[i]'h₂)
