import AFTD.Prelude
import AFTD.Kb.Tcs.Depth3SigmoidCircuit

/-!
# depth3_sigmoid_circuit_eval

Topic: circuits   Node: c87789b7cebb

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:709

Evaluates a depth-3 sigmoidal circuit C on a real input vector x : Fin n → ℝ using Real.sigmoid: layer 1 computes Real.sigmoid ((∑ i : Fin n, C.w₁ j i * x i) + C.b₁ j), layer 2 computes Real.sigmoid ((∑ j : Fin C.m₁, C.w₂ k j * layer1 j) + C.b₂ k), and the output gate computes Real.sigmoid ((∑ k : Fin C.m₂, C.w₃ k * layer2 k) + C.b₃), where each bias is added once to the inner product outside the summation.
-/

/-- Evaluation of a depth-3 sigmoidal circuit on a real input vector. -/
noncomputable def depth3_sigmoid_circuit_eval {n : ℕ} (C : Depth3SigmoidCircuit n) (x : Fin n → ℝ) : ℝ :=
  let layer1 : Fin C.m₁ → ℝ := fun j => Real.sigmoid ((∑ i : Fin n, C.w₁ j i * x i) + C.b₁ j)
  let layer2 : Fin C.m₂ → ℝ := fun k => Real.sigmoid ((∑ j : Fin C.m₁, C.w₂ k j * layer1 j) + C.b₂ k)
  Real.sigmoid ((∑ k : Fin C.m₂, C.w₃ k * layer2 k) + C.b₃)
