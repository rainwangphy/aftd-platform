import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc
import AFTD.Kb.Optimization.IsSubmodularCube
import AFTD.Kb.Optimization.CubeDist

/-!
# is_far_from_submodular

Topic: submodular   Node: 6dc5b4e75383

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.4

A function f is ε-far from submodular if its normalized Hamming distance to every submodular function g with the same domain and codomain is at least ε.
-/

/-- A function is ε-far from submodular if every submodular function disagrees on at least an ε fraction of inputs. -/
def is_far_from_submodular {n k : ℕ} (ε : ℝ) (f : CubeFunc n k) : Prop := ∀ g : CubeFunc n k, is_submodular_cube g → ε ≤ cube_dist f g
