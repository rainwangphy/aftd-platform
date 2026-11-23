import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.PowerRelationCarrier
import AFTD.Kb.GameTheoryEconomics.PowerRelationRel

/-!
# is_merging_sum_power_relation

Topic: social_choice   Node: 0a8d5e6e9bc0

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 4(1)

A power relation r is a merging sum of two power relations r₁ and r₂ with disjoint coalition domains if the carrier of r is the union of their carriers and r agrees with r₁ on the carrier of r₁ and with r₂ on the carrier of r₂.
-/

/-- A power relation is a merging sum of two power relations on disjoint domains if its domain is their union and its restriction to each domain agrees with the original. -/
def is_merging_sum_power_relation {X : Type*} (r r₁ r₂ : PowerRelation X) : Prop := Disjoint (power_relation_carrier r₁) (power_relation_carrier r₂) ∧
  power_relation_carrier r = power_relation_carrier r₁ ∪ power_relation_carrier r₂ ∧
  (∀ S ∈ power_relation_carrier r₁, ∀ T ∈ power_relation_carrier r₁,
    power_relation_rel r S T ↔ power_relation_rel r₁ S T) ∧
  (∀ S ∈ power_relation_carrier r₂, ∀ T ∈ power_relation_carrier r₂,
    power_relation_rel r S T ↔ power_relation_rel r₂ S T)
