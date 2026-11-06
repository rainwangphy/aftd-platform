import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularBounded
import AFTD.Kb.Optimization.HypercubeRelDist

/-!
# is_eps_far_submodular

Topic: submodular   Node: 95f6b4cf1880

Provenance: formalization of a published result. Source: arXiv:2611.02374 Def. 2.4

A function f from Fin n → Bool to Fin (k + 1) is ε-far from submodularity if for every submodular function g from Fin n → Bool to Fin (k + 1), the relative Hamming distance between f and g is at least ε.
-/

/-- A function from Fin n → Bool to Fin (k + 1) is ε-far from submodular if its relative distance to every submodular function is at least ε. -/
def is_eps_far_submodular (n k : ℕ) (ε : ℝ) (f : (Fin n → Bool) → Fin (k + 1)) : Prop :=
  ∀ g : (Fin n → Bool) → Fin (k + 1), is_submodular_bounded n k g → ε ≤ hypercube_rel_dist f g
