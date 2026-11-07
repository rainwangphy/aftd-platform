import AFTD.Prelude

/-!
# partial_assignment_le

Topic: submodular   Node: a5e579d3d7c8

Provenance: formalization of a published result. Source: scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:262

A partial assignment β is extended by γ (written β ≼ γ) if for every element e and boolean value b, β(e) = some b implies γ(e) = some b.
-/

/-- A partial assignment is extended by another if every defined edge value is preserved. -/
def partial_assignment_le {E : Type*} (β γ : E → Option Bool) : Prop := ∀ e b, β e = some b → γ e = some b
