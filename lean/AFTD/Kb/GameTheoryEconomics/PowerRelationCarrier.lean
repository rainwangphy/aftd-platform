import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# power_relation_carrier

Topic: social_choice   Node: d6134aa3a24c

Provenance: formalization of a published result. Source: arXiv:2611.19021 Section 2.1

The carrier of a power relation r is the set of all coalitions appearing in some equivalence class of r.
-/

/-- The domain of feasible coalitions of a power relation. -/
def power_relation_carrier {X : Type*} (r : PowerRelation X) : Set (Finset X) := {S | ∃ c ∈ r.classes, S ∈ c}
