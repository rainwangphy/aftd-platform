import AFTD.Prelude

/-!
# Depth3SigmoidCircuit

Topic: circuits   Node: 79fe141cee47

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:709

A feedforward circuit structure on n inputs parameterized solely by the input dimension n : ℕ, containing internal fields for the hidden layer sizes m₁, m₂ : ℕ, weight matrices w₁ : Fin m₁ → Fin n → ℝ and w₂ : Fin m₂ → Fin m₁ → ℝ, bias vectors b₁ : Fin m₁ → ℝ and b₂ : Fin m₂ → ℝ, an output weight vector w₃ : Fin m₂ → ℝ, and an output bias scalar b₃ : ℝ.
-/

/-- Feedforward depth-3 circuit structure on n inputs storing layer dimensions, weights, and biases. -/
structure Depth3SigmoidCircuit (n : ℕ) where
  m₁ : ℕ
  m₂ : ℕ
  w₁ : Fin m₁ → Fin n → ℝ
  b₁ : Fin m₁ → ℝ
  w₂ : Fin m₂ → Fin m₁ → ℝ
  b₂ : Fin m₂ → ℝ
  w₃ : Fin m₂ → ℝ
  b₃ : ℝ
