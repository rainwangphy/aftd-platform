import AFTD.Prelude
import AFTD.Kb.Tcs.Depth3SigmoidCircuit

/-!
# depth3_sigmoid_circuit_weights_bounded_by

Topic: circuits   Node: 3ba27af754ab

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:743

Predicate stating that every weight in w₁, w₂, w₃ and every bias in b₁, b₂, b₃ of a depth-3 circuit C has absolute value at most B.
-/

/-- Property that all weights and biases in a depth-3 sigmoidal circuit are bounded by B in absolute value. -/
def depth3_sigmoid_circuit_weights_bounded_by {n : ℕ} (C : Depth3SigmoidCircuit n) (B : ℝ) : Prop :=
  (∀ j i, |C.w₁ j i| ≤ B) ∧ (∀ j, |C.b₁ j| ≤ B) ∧
  (∀ k j, |C.w₂ k j| ≤ B) ∧ (∀ k, |C.b₂ k| ≤ B) ∧
  (∀ k, |C.w₃ k| ≤ B) ∧ |C.b₃| ≤ B
