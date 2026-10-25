import AFTD.Prelude
import AFTD.Kb.Tcs.ReLUHiddenLayer
import AFTD.Kb.Tcs.Relu

/-!
# evalHiddenLayer

Topic: np_completeness   Node: 70b689fd1998

Provenance: formalization of a published result. Source: arXiv:2610.06092 Section 2.1

Evaluation of a hidden layer of width $k$ on an input vector $x \in \mathbb{R}^k$, computing for each neuron $i$ the rectified linear unit of the affine combination: the sum over $j$ of the weight matrix entry times $x_j$, plus the bias of neuron $i$.
-/

/-- Evaluate a single ReLU hidden layer on an input vector. -/
def evalHiddenLayer {k : ℕ} (layer : ReLUHiddenLayer k) (x : Fin k → ℝ) : Fin k → ℝ := fun i => relu ((∑ j, (layer.weight i j : ℝ) * x j) + (layer.bias i : ℝ))
