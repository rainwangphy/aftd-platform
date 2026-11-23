import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# power_relation_rel

Topic: social_choice   Node: 80d6314e9800

Provenance: formalization of a published result. Source: arXiv:2611.19021 Section 2.1

Coalition S is weakly preferred to coalition T under power relation r if the equivalence class of S is ranked at least as high as that of T.
-/

/-- Weak preference relation on coalitions induced by a power relation. -/
def power_relation_rel {X : Type*} (r : PowerRelation X) (S T : Finset X) : Prop := ∃ (i j : ℕ) (hi : i < r.classes.length) (hj : j < r.classes.length),
    S ∈ r.classes[i]'hi ∧ T ∈ r.classes[j]'hj ∧ i ≤ j
