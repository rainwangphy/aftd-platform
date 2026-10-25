import AFTD.Prelude
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# evalNetwork

Topic: np_completeness   Node: 58da4d89588b

Provenance: formalization of a published result. Source: arXiv:2610.06092 Section 2.1

Evaluation of a feedforward ReLU neural network of hidden layer width $k$ on a real input $x$, which forms an initial width-$k$ vector by applying input weights and biases to $x$, iteratively updates the vector through each hidden layer using evalHiddenLayer, and computes the final scalar by taking the inner product with output weights and adding the output bias.
-/

/-- Evaluate a feedforward ReLU neural network on a real input. -/
def evalNetwork {k : ℕ} (net : ReLUNetwork k) (x : ℝ) : ℝ := let x0 : Fin k → ℝ := fun i => (net.in_weight i : ℝ) * x + (net.in_bias i : ℝ)
  let x_hidden := net.layers.foldl (fun v l => evalHiddenLayer l v) x0
  (∑ i, (net.out_weight i : ℝ) * x_hidden i) + (net.out_bias : ℝ)
