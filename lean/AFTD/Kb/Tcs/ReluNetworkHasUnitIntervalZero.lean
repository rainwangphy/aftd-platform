import AFTD.Prelude
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.ReLUNetwork

/-!
# relu_network_has_unit_interval_zero

Topic: np_completeness   Node: 37b27ccf9bf7

Provenance: formalization of a published result. Source: arXiv:2610.06092 Corollary 5.12

A feedforward ReLU neural network `net` of width $k$ has a zero in the unit interval $[0, 1]$ if there exists some real number $x \in [0, 1]$ such that `evalNetwork net x = 0`.
-/

/-- Predicate asserting that a feedforward ReLU network has a root in the unit interval [0,1]. -/
def relu_network_has_unit_interval_zero {k : ℕ} (net : ReLUNetwork k) : Prop := ∃ x ∈ Set.Icc (0 : ℝ) 1, evalNetwork net x = 0
